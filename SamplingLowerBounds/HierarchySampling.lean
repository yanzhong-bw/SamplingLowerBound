import SamplingLowerBounds.CoordinateEncoding
import SamplingLowerBounds.AndBlocks
import SamplingLowerBounds.DyadicSampling
import SamplingLowerBounds.AndPolynomialBridge

/-!
# The canonical N-bit adjacent-degree hierarchy

The target is the actual flat graph of disjoint AND gates and padding, encoded
by an explicit permutation of bit coordinates. Its lower bound applies to
every actual polynomial source on an arbitrary number of uniform input bits.
No external acceptance-gap theorem is needed.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.FlatGraph
open PolynomialModel Information CubeTilt

noncomputable section

/-- Uniform pushforwards do not depend on the chosen finite enumeration.
Making this equality explicit also avoids elaborator reduction of the full
enumeration when instantiating a generic finite-type theorem at bit vectors. -/
theorem uniform_push_fintype {A B : Type*} (i₁ i₂ : Fintype A) (f : A → B) (b : B) :
    @pushMass A B i₁ (@uniformMass A i₁) f b =
      @pushMass A B i₂ (@uniformMass A i₂) f b := by
  cases Subsingleton.elim i₁ i₂
  rfl

/-- Actual law of the padded AND graph, expressed on ordinary N-bit strings. -/
def paddedTarget (d m u v N : ℕ) (hsize : m*(d+1)+u+(m+v) = N) :
    (Fin N → Bool) → ℝ :=
  pushMass
    (graphLaw (paddedAND (I := Fin m) (J := Fin (d+1)) (K := Fin u) (L := Fin v)))
    (coordinateEncoding m (d+1) u v N hsize)

theorem paddedTarget_at_encoding (d m u v N : ℕ)
    (hsize : m*(d+1)+u+(m+v) = N) (z : StructuredOutput m (d+1) u v) :
    paddedTarget d m u v N hsize (coordinateEncoding m (d+1) u v N hsize z) =
      graphLaw (paddedAND (I := Fin m) (J := Fin (d+1)) (K := Fin u) (L := Fin v)) z :=
  pushMass_injective_at _ _ (coordinateEncoding m (d+1) u v N hsize).injective z

theorem paddedTarget_nonneg (d m u v N : ℕ) (hsize : m*(d+1)+u+(m+v) = N)
    (y : Fin N → Bool) : 0 ≤ paddedTarget d m u v N hsize y :=
  pushMass_nonneg _ _ (graphLaw_nonneg paddedAND) y

theorem paddedTarget_sum (d m u v N : ℕ) (hsize : m*(d+1)+u+(m+v) = N) :
    (∑ y, paddedTarget d m u v N hsize y) = 1 := by
  rw [paddedTarget, pushMass_sum]
  exact graphLaw_sum paddedAND

theorem paddedTarget_flat (d m u v N : ℕ) (hsize : m*(d+1)+u+(m+v) = N)
    (y : Fin N → Bool) :
    paddedTarget d m u v N hsize y = 0 ∨
      paddedTarget d m u v N hsize y = 1/(2:ℝ)^(m*(d+1)+u) := by
  let e := coordinateEncoding m (d+1) u v N hsize
  obtain ⟨z, rfl⟩ := e.surjective y
  rw [paddedTarget_at_encoding]
  rcases z with ⟨x,b⟩
  rw [graphLaw_mass]
  split_ifs
  · right
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    rw [← pow_mul, Nat.mul_comm (d+1), ← pow_add]
  · exact Or.inl rfl

/-- Projecting the target's active coordinates gives exactly the dyadic
Bernoulli product law used by the unconditional sampling lower bound. -/
theorem paddedTarget_active_law (d m u v N : ℕ)
    (hsize : m*(d+1)+u+(m+v) = N) :
    pushMass (paddedTarget d m u v N hsize)
      (fun y i => y (activeIndex m (d+1) u v N hsize i)) =
      bernoulliProduct (1/(2:ℝ)^(d+1)) := by
  funext y
  rw [paddedTarget, pushMass_comp]
  have hc :
      (fun y i => y (activeIndex m (d+1) u v N hsize i)) ∘
        coordinateEncoding m (d+1) u v N hsize =
      (Prod.fst ∘ Prod.snd : StructuredOutput m (d+1) u v → Fin m → Bool) := by
    funext z i
    exact coordinateEncoding_active m (d+1) u v N hsize z i
  rw [hc, ← pushMass_comp]
  have hlabel :
      pushMass (graphLaw (paddedAND (I := Fin m) (J := Fin (d+1)) (K := Fin u) (L := Fin v)))
        Prod.snd = pushMass (uniformMass _) paddedAND :=
    funext (graphLaw_label_projection paddedAND)
  calc
    _ = pushMass
        (pushMass (uniformMass ((Fin m → Fin (d+1) → Bool) × (Fin u → Bool)))
          (paddedAND (L := Fin v))) Prod.fst y :=
      congrArg (fun R => pushMass R Prod.fst y) hlabel
    _ = pushMass (uniformMass ((Fin m → Fin (d+1) → Bool) × (Fin u → Bool)))
        (Prod.fst ∘ (paddedAND (L := Fin v))) y :=
      pushMass_comp _ _ _ _
    _ = _ := by
      have ha :=
        paddedAND_active_law (I := Fin m) (J := Fin (d+1)) (K := Fin u) (L := Fin v) y
      rw [Fintype.card_fin] at ha
      exact (uniform_push_fintype _ _ _ _).trans ha

/-- Full unconditional lower bound for the concrete N-bit padded-AND target. -/
theorem paddedTarget_overlap {s N d m u v : ℕ}
    (hsize : m*(d+1)+u+(m+v) = N) (Q : Source s N d) :
    overlap Q.boolEval (paddedTarget d m u v N hsize) ≤
      Real.exp (-((m:ℝ)/(2:ℝ)^(3*d+10))) := by
  let f : Fin m → Fin N := activeIndex m (d+1) u v N hsize
  have h := massOverlap_postprocess (outputLaw Q.boolEval) (paddedTarget d m u v N hsize)
    (fun y i => y (f i))
  rw [Source.project_outputLaw] at h
  have ht : pushMass (paddedTarget d m u v N hsize) (fun y i => y (f i)) =
      bernoulliProduct (1/(2:ℝ)^(d+1)) := paddedTarget_active_law d m u v N hsize
  rw [ht] at h
  exact h.trans (dyadic_overlap (Q.project f))

theorem hierarchy_size (d N k : ℕ) (hk : k ≤ N) :
    hierarchyBlocks d N k * (d+1) + (k-hierarchyBlocks d N k*(d+1)) +
      (hierarchyBlocks d N k + (N-k-hierarchyBlocks d N k)) = N := by
  have hseed := hierarchyBlocks_seed_bound d N k
  have hlabel := hierarchyBlocks_label_bound d N k
  omega

/-- The precise N-bit target distribution at prescribed entropy k. -/
def hierarchyTarget (d N k : ℕ) (hk : k ≤ N) : (Fin N → Bool) → ℝ :=
  paddedTarget d (hierarchyBlocks d N k)
    (k-hierarchyBlocks d N k*(d+1)) (N-k-hierarchyBlocks d N k) N
    (hierarchy_size d N k hk)

theorem hierarchyTarget_nonneg (d N k : ℕ) (hk : k ≤ N) (y : Fin N → Bool) :
    0 ≤ hierarchyTarget d N k hk y :=
  paddedTarget_nonneg _ _ _ _ _ _ y

theorem hierarchyTarget_sum (d N k : ℕ) (hk : k ≤ N) :
    (∑ y, hierarchyTarget d N k hk y) = 1 := paddedTarget_sum _ _ _ _ _ _

/-- Every nonzero atom has probability exactly 2^(-k), so this normalized
distribution is flat at the prescribed entropy. -/
theorem hierarchyTarget_flat (d N k : ℕ) (hk : k ≤ N) (y : Fin N → Bool) :
    hierarchyTarget d N k hk y = 0 ∨ hierarchyTarget d N k hk y = 1/(2:ℝ)^k := by
  have h := paddedTarget_flat d (hierarchyBlocks d N k)
    (k-hierarchyBlocks d N k*(d+1)) (N-k-hierarchyBlocks d N k) N
    (hierarchy_size d N k hk) y
  have he : hierarchyBlocks d N k*(d+1)+(k-hierarchyBlocks d N k*(d+1)) = k :=
    Nat.add_sub_of_le (hierarchyBlocks_seed_bound d N k)
  rwa [he] at h

/-- The target is sampled by an actual degree-at-most-(d+1) polynomial map
on exactly k uniform input bits, with explicit coordinate formulas. -/
def hierarchySampler (d N k : ℕ) (hk : k ≤ N) : Source k N (d+1) :=
  canonicalANDSource (hierarchyBlocks d N k) d
    (k-hierarchyBlocks d N k*(d+1)) (N-k-hierarchyBlocks d N k) k N
    (Nat.add_sub_of_le (hierarchyBlocks_seed_bound d N k)) (hierarchy_size d N k hk)

theorem hierarchySampler_outputLaw (d N k : ℕ) (hk : k ≤ N) :
    outputLaw (hierarchySampler d N k hk).boolEval = hierarchyTarget d N k hk :=
  canonicalANDSource_outputLaw _ _ _ _ _ _ _ _

theorem hierarchySampler_exact_degree_of_blocks (d N k : ℕ) (hk : k ≤ N)
    (hm : 0 < hierarchyBlocks d N k) :
    ∃ j, ((hierarchySampler d N k hk).coordinate j).totalDegree = d+1 :=
  canonicalANDSource_exact_degree _ _ _ _ _ _ _ _ hm

theorem hierarchySampler_exact_degree (d N k : ℕ) (hk : k ≤ N)
    (hs : 2*(d+1) ≤ min k (N-k)) :
    ∃ j, ((hierarchySampler d N k hk).coordinate j).totalDegree = d+1 := by
  apply canonicalANDSource_exact_degree
  have h := hierarchyBlocks_entropy_bound_nat d N k hs
  by_contra hn
  have hz : hierarchyBlocks d N k = 0 := Nat.eq_zero_of_not_pos hn
  rw [hz] at h
  omega

/-- The canonical source has locality at most d+1. -/
theorem hierarchySampler_locality (d N k : ℕ) (hk : k ≤ N) (j : Fin N) :
    ∃ S : Finset (Fin k), S.card ≤ d+1 ∧
      ∀ (x y : Fin k → F₂), (∀ a ∈ S, x a = y a) →
        (hierarchySampler d N k hk).boolEval x j =
          (hierarchySampler d N k hk).boolEval y j := by
  let hkseed := Nat.add_sub_of_le (hierarchyBlocks_seed_bound d N k)
  let hN := hierarchy_size d N k hk
  refine ⟨canonicalDependencies (hierarchyBlocks d N k) d
    (k-hierarchyBlocks d N k*(d+1)) (N-k-hierarchyBlocks d N k) k N hkseed hN j,
    canonicalDependencies_card _ _ _ _ _ _ _ _ _, ?_⟩
  intro x y hxy
  exact canonicalANDSource_locality _ _ _ _ _ _ _ _ j x y hxy

/-- The exact active-block exponent for every seed length. -/
theorem hierarchy_overlap {s N d k : ℕ} (hk : k ≤ N) (Q : Source s N d) :
    overlap Q.boolEval (hierarchyTarget d N k hk) ≤
      Real.exp (-((hierarchyBlocks d N k : ℝ)/(2:ℝ)^(3*d+10))) :=
  paddedTarget_overlap (hierarchy_size d N k hk) Q

/-- The stated exponential dependence on the smaller of entropy and
codimension, including all padding and integer-rounding losses. -/
theorem hierarchy_entropy_overlap {s N d k : ℕ} (hk : k ≤ N)
    (hs : 2*(d+1) ≤ min k (N-k)) (Q : Source s N d) :
    overlap Q.boolEval (hierarchyTarget d N k hk) ≤
      Real.exp (-((min k (N-k) : ℕ) : ℝ) /
        (2*((d:ℝ)+1)*(2:ℝ)^(3*d+10))) := by
  apply (hierarchy_overlap hk Q).trans
  apply Real.exp_le_exp.mpr
  have hm := hierarchyBlocks_entropy_bound d N k hs
  have hp : 0 < (2:ℝ)^(3*d+10) := by positivity
  have h := div_le_div_of_nonneg_right hm hp.le
  rw [div_div] at h
  simpa only [neg_div] using neg_le_neg h

end
end SamplingLowerBounds.FlatGraph
