import SamplingLowerBounds.AndPolynomial
import SamplingLowerBounds.AndBlocks
import SamplingLowerBounds.CoordinateEncoding

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.PolynomialModel

open FlatGraph
noncomputable section

theorem bool_product_eq_AND {J : Type*} [Fintype J] (x : J → Bool) :
    (∏ j, boolEquivF₂ (x j)) = boolEquivF₂ (blockAND x) := by
  by_cases h : ∀ j, x j = true
  · have hp : (∏ j, boolEquivF₂ (x j)) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      simp [h j, boolEquivF₂]
    rw [hp]
    simp [blockAND, h, boolEquivF₂]
  · have hex : ∃ j, x j = false := by
      push_neg at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, Bool.eq_false_iff.mpr hj⟩
    obtain ⟨j, hj⟩ := hex
    have hp : (∏ j, boolEquivF₂ (x j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj, boolEquivF₂]
    rw [hp]
    simp [blockAND, h, boolEquivF₂]

def fieldAssignment {I J K : Type*}
    (x : (I → J → Bool) × (K → Bool)) : BlockVariables I J K → F₂ :=
  Sum.elim (fun ij => boolEquivF₂ (x.1 ij.1 ij.2)) (fun k => boolEquivF₂ (x.2 k))

theorem eval_paddedAND_label {I J K L : Type*} [Fintype J]
    (x : (I → J → Bool) × (K → Bool)) (i : BlockLabels I L) :
    MvPolynomial.eval (fieldAssignment x) (paddedLabelPolynomial i) =
      boolEquivF₂ (Sum.elim (paddedAND (L := L) x).1 (paddedAND (L := L) x).2 i) := by
  cases i with
  | inl i =>
    simpa only [paddedLabelPolynomial, Sum.elim_inl, eval_blockPolynomial,
      fieldAssignment, paddedAND, disjointAND] using bool_product_eq_AND (x.1 i)
  | inr i => simp [paddedLabelPolynomial, paddedAND, boolEquivF₂]

theorem eval_graphPolynomial_bits (m b u v : ℕ)
    (x : (Fin m → Fin b → Bool) × (Fin u → Bool))
    (i : StructuredIndex m b u v) :
    MvPolynomial.eval (fieldAssignment x) (graphPolynomial i) =
      boolEquivF₂ (structuredBits m b u v (graphMap paddedAND x) i) := by
  cases i with
  | inl i =>
    cases i <;> simp [graphPolynomial, fieldAssignment, structuredBits, graphMap]
  | inr i =>
    exact eval_paddedAND_label x i

def seedIndexEquiv (m b u k : ℕ) (hsize : m*b+u=k) :
    BlockVariables (Fin m) (Fin b) (Fin u) ≃ Fin k :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin u))).trans finSumFinEquiv).trans
    (finCongr hsize)

/-- An explicit coordinate splitting of the ordinary `k` seed bits. -/
def splitSeed (m b u k : ℕ) (hsize : m*b+u=k) (x : Fin k → Bool) :
    (Fin m → Fin b → Bool) × (Fin u → Bool) :=
  ((fun i j => x (seedIndexEquiv m b u k hsize (.inl (i,j)))),
    fun j => x (seedIndexEquiv m b u k hsize (.inr j)))

/-- The ordinary `k`-input, `N`-output polynomial graph sampler. -/
def canonicalANDSource (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) : Source k N (d+1) where
  coordinate j := MvPolynomial.renameEquiv F₂ (seedIndexEquiv m (d+1) u k hk)
    (graphPolynomial ((structuredIndexEquiv m (d+1) u v N hN).symm j))
  degree_le j := by
    rw [MvPolynomial.totalDegree_renameEquiv]
    simpa only [Fintype.card_fin] using
      graphPolynomial_degree_le (I := Fin m) (J := Fin (d+1))
        (K := Fin u) (L := Fin v) ((structuredIndexEquiv m (d+1) u v N hN).symm j)

theorem canonicalANDSource_exact_degree (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (hm : 0 < m) :
    ∃ j, ((canonicalANDSource m d u v k N hk hN).coordinate j).totalDegree = d+1 := by
  refine ⟨structuredIndexEquiv m (d+1) u v N hN (.inr (.inl ⟨0,hm⟩)), ?_⟩
  simp only [canonicalANDSource, Equiv.symm_apply_apply, MvPolynomial.totalDegree_renameEquiv]
  simpa only [Fintype.card_fin] using
    paddedLabelPolynomial_active_degree (J := Fin (d+1))
      (K := Fin u) (L := Fin v) (⟨0,hm⟩ : Fin m)

theorem canonicalANDSource_boolEval (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (x : Fin k → Bool) :
    (canonicalANDSource m d u v k N hk hN).boolEval (fun j => boolEquivF₂ (x j)) =
      coordinateEncoding m (d+1) u v N hN
        (graphMap paddedAND (splitSeed m (d+1) u k hk x)) := by
  funext j
  have hf : (fun j => boolEquivF₂ (x j)) ∘ seedIndexEquiv m (d+1) u k hk =
      fieldAssignment (splitSeed m (d+1) u k hk x) := by
    funext i
    cases i <;> rfl
  have he := eval_graphPolynomial_bits m (d+1) u v
    (splitSeed m (d+1) u k hk x) ((structuredIndexEquiv m (d+1) u v N hN).symm j)
  have hv : MvPolynomial.eval (fun j => boolEquivF₂ (x j))
      ((canonicalANDSource m d u v k N hk hN).coordinate j) =
      boolEquivF₂ (coordinateEncoding m (d+1) u v N hN
        (graphMap paddedAND (splitSeed m (d+1) u k hk x)) j) := by
    change MvPolynomial.eval _ (MvPolynomial.rename _ _) = _
    rw [MvPolynomial.eval_rename, hf]
    exact he
  change boolEquivF₂.symm (MvPolynomial.eval _ _) = _
  rw [hv, Equiv.symm_apply_apply]

def seedBits (m b u : ℕ) :
    ((Fin m → Fin b → Bool) × (Fin u → Bool)) ≃
      (BlockVariables (Fin m) (Fin b) (Fin u) → Bool) where
  toFun x := Sum.elim (fun ij => x.1 ij.1 ij.2) x.2
  invFun f := ((fun i j => f (.inl (i,j))), fun j => f (.inr j))
  left_inv _ := rfl
  right_inv f := by funext i; cases i <;> rfl

def splitSeedEquiv (m b u k : ℕ) (hsize : m*b+u=k) :
    (Fin k → Bool) ≃ ((Fin m → Fin b → Bool) × (Fin u → Bool)) :=
  ((seedBits m b u).trans
    (Equiv.arrowCongr (seedIndexEquiv m b u k hsize) (Equiv.refl Bool))).symm

theorem splitSeed_uniform (m b u k : ℕ) (hsize : m*b+u=k) :
    Information.pushMass (CubeTilt.uniformMass (Fin k → Bool)) (splitSeed m b u k hsize) =
      CubeTilt.uniformMass ((Fin m → Fin b → Bool) × (Fin u → Bool)) := by
  have he : splitSeed m b u k hsize = splitSeedEquiv m b u k hsize := rfl
  rw [he]
  exact uniformMass_equiv _

/-- The canonical polynomial sampler has exactly the encoded padded graph law. -/
theorem canonicalANDSource_outputLaw (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) :
    CubeTilt.outputLaw (canonicalANDSource m d u v k N hk hN).boolEval =
      Information.pushMass
        (graphLaw (paddedAND (I := Fin m) (J := Fin (d+1)) (K := Fin u) (L := Fin v)))
        (coordinateEncoding m (d+1) u v N hN) := by
  let E : (Fin k → Bool) ≃ (Fin k → F₂) :=
    Equiv.piCongrRight (fun _ => boolEquivF₂)
  let Q := canonicalANDSource m d u v k N hk hN
  let e := coordinateEncoding m (d+1) u v N hN
  let f := splitSeed m (d+1) u k hk
  have hmap : Q.boolEval ∘ E = e ∘ graphMap paddedAND ∘ f := by
    funext x
    exact canonicalANDSource_boolEval m d u v k N hk hN x
  rw [outputLaw_eq_pushMass]
  change Information.pushMass (CubeTilt.uniformMass (Fin k → F₂)) Q.boolEval = _
  calc
    _ = Information.pushMass
        (Information.pushMass (CubeTilt.uniformMass (Fin k → Bool)) E) Q.boolEval := by
      rw [uniformMass_equiv]
    _ = Information.pushMass (CubeTilt.uniformMass (Fin k → Bool)) (Q.boolEval ∘ E) :=
      funext (fun y => pushMass_comp _ _ _ y)
    _ = Information.pushMass (CubeTilt.uniformMass (Fin k → Bool))
        (e ∘ graphMap paddedAND ∘ f) := by rw [hmap]
    _ = Information.pushMass
        (Information.pushMass (CubeTilt.uniformMass (Fin k → Bool)) f)
        (e ∘ graphMap paddedAND) :=
      funext (fun y => (pushMass_comp (CubeTilt.uniformMass (Fin k → Bool))
        f (e ∘ graphMap paddedAND) y).symm)
    _ = Information.pushMass
        (CubeTilt.uniformMass ((Fin m → Fin (d+1) → Bool) × (Fin u → Bool)))
        (e ∘ graphMap paddedAND) := by rw [splitSeed_uniform]
    _ = _ := funext (fun y => (pushMass_comp _ _ _ y).symm)

/-- The exact input coordinates used by one canonical graph output. -/
def canonicalDependencies (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (j : Fin N) : Finset (Fin k) :=
  match (structuredIndexEquiv m (d+1) u v N hN).symm j with
  | .inl a => {seedIndexEquiv m (d+1) u k hk a}
  | .inr (.inl i) => Finset.univ.image (fun l => seedIndexEquiv m (d+1) u k hk (.inl (i,l)))
  | .inr (.inr _) => ∅

theorem canonicalDependencies_card (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (j : Fin N) :
    (canonicalDependencies m d u v k N hk hN j).card ≤ d+1 := by
  unfold canonicalDependencies
  cases (structuredIndexEquiv m (d+1) u v N hN).symm j with
  | inl a => simp
  | inr a =>
    cases a with
    | inl i => exact (Finset.card_image_le).trans (by simp)
    | inr i => simp

/-- Every output bit depends on at most d+1 seed bits, including all padding. -/
theorem canonicalANDSource_locality (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (j : Fin N)
    (x y : Fin k → F₂)
    (hxy : ∀ a ∈ canonicalDependencies m d u v k N hk hN j, x a = y a) :
    (canonicalANDSource m d u v k N hk hN).boolEval x j =
      (canonicalANDSource m d u v k N hk hN).boolEval y j := by
  have hv : (canonicalANDSource m d u v k N hk hN).eval x j =
      (canonicalANDSource m d u v k N hk hN).eval y j := by
    change MvPolynomial.eval x (MvPolynomial.rename _ _) =
      MvPolynomial.eval y (MvPolynomial.rename _ _)
    rw [MvPolynomial.eval_rename, MvPolynomial.eval_rename]
    cases hi : (structuredIndexEquiv m (d+1) u v N hN).symm j with
    | inl a =>
      simp only [graphPolynomial, Sum.elim_inl, MvPolynomial.eval_X, Function.comp_apply]
      apply hxy
      simp [canonicalDependencies, hi]
    | inr a =>
      cases a with
      | inl i =>
        simp only [graphPolynomial, Sum.elim_inr, paddedLabelPolynomial, Sum.elim_inl,
          eval_blockPolynomial, Function.comp_apply]
        apply Finset.prod_congr rfl
        intro l _
        apply hxy
        simp [canonicalDependencies, hi]
      | inr i => simp [graphPolynomial, paddedLabelPolynomial]
  simp only [Source.boolEval, hv]

end

/-- Executable Boolean sampler: split the seed, evaluate the disjoint AND
blocks, retain the seed, append zero labels, and permute coordinates. -/
def canonicalSampler (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (x : Fin k → Bool) : Fin N → Bool :=
  coordinateEncoding m (d+1) u v N hN
    (graphMap paddedAND (splitSeed m (d+1) u k hk x))

theorem canonicalSampler_is_polynomial (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (x : Fin k → Bool) :
    canonicalSampler m d u v k N hk hN x =
      (canonicalANDSource m d u v k N hk hN).boolEval (fun j => boolEquivF₂ (x j)) :=
  (canonicalANDSource_boolEval m d u v k N hk hN x).symm

end SamplingLowerBounds.PolynomialModel
