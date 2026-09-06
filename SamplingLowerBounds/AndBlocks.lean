import SamplingLowerBounds.FlatGraph
import SamplingLowerBounds.BernoulliTests

/-!
# The exact output law of disjoint AND blocks

The seed is the actual uniform law on the block input matrix.  Independence
of the output coordinates follows by summing the product law over its fibres.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.FlatGraph

open Information CubeTilt

theorem pushMass_product {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    (P : I → A → ℝ) (f : I → A → B) (y : I → B) :
    pushMass (productMass P) (fun x i => f i (x i)) y =
      productMass (fun i => pushMass (P i) (f i)) y := by
  have hpoint (x : I → A) :
      (if (fun i => f i (x i)) = y then ∏ i, P i (x i) else 0) =
        ∏ i, if f i (x i) = y i then P i (x i) else 0 := by
    by_cases h : (fun i => f i (x i)) = y
    · have hi (i : I) : f i (x i) = y i := congrFun h i
      simp only [if_pos h, hi, ↓reduceIte]
    · rw [if_neg h]
      have hi : ∃ i, f i (x i) ≠ y i := by
        by_contra hn
        push_neg at hn
        exact h (funext hn)
      obtain ⟨i, hi⟩ := hi
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_neg hi
  simp only [pushMass, productMass]
  simp_rw [hpoint]
  exact (Fintype.prod_sum (fun i a => if f i a = y i then P i a else 0)).symm

theorem uniformMass_function {I A : Type*} [Fintype I] [Fintype A] (x : I → A) :
    uniformMass (I → A) x = productMass (fun _ : I => uniformMass A) x := by
  simp [uniformMass, productMass, Fintype.card_fun]

def blockAND {J : Type*} [Fintype J] (x : J → Bool) : Bool :=
  decide (∀ j, x j = true)

theorem blockAND_true_iff {J : Type*} [Fintype J] (x : J → Bool) :
    blockAND x = true ↔ x = fun _ => true := by
  simp only [blockAND, decide_eq_true_eq]
  exact ⟨funext, fun h j => congrFun h j⟩

theorem blockAND_true_mass {J : Type*} [Fintype J] :
    pushMass (uniformMass (J → Bool)) blockAND true =
      1 / (2 : ℝ) ^ Fintype.card J := by
  simp only [pushMass, blockAND_true_iff, uniformMass]
  simp

/-- One AND gate on `|J|` independent bits has bias `2^(-|J|)`. -/
theorem blockAND_law {J : Type*} [Fintype J] (b : Bool) :
    pushMass (uniformMass (J → Bool)) blockAND b =
      bernoulliMass (1 / (2 : ℝ) ^ Fintype.card J) b := by
  have ht := blockAND_true_mass (J := J)
  have hs := pushMass_sum (uniformMass (J → Bool)) (blockAND (J := J))
  rw [uniformMass_sum, Fintype.sum_bool] at hs
  cases b
  · simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte]
    linarith
  · simpa only [bernoulliMass, ↓reduceIte] using ht

def disjointAND {I J : Type*} [Fintype J] (x : I → J → Bool) (i : I) : Bool :=
  blockAND (x i)

/-- The entire disjoint-AND output law is the required Bernoulli product. -/
theorem disjointAND_law {I J : Type*} [Fintype I] [Fintype J] (y : I → Bool) :
    pushMass (uniformMass (I → J → Bool)) disjointAND y =
      productMass (fun _ : I => bernoulliMass (1 / (2 : ℝ) ^ Fintype.card J)) y := by
  have he : uniformMass (I → J → Bool) =
      productMass (fun _ : I => uniformMass (J → Bool)) :=
    funext uniformMass_function
  rw [he]
  change pushMass _ (fun (x : I → J → Bool) i => blockAND (x i)) y = _
  rw [pushMass_product]
  unfold productMass
  apply Finset.prod_congr rfl
  intro i _
  exact blockAND_law (y i)

/-- Separation from the AND product lifts to its flat graph target. -/
theorem overlap_disjointAND_graph_le {I J : Type*} [Fintype I] [Fintype J]
    (P : (I → J → Bool) × (I → Bool) → ℝ) :
    massOverlap P (graphLaw disjointAND) ≤
      massOverlap (pushMass P Prod.snd)
        (productMass (fun _ : I => bernoulliMass (1 / (2 : ℝ) ^ Fintype.card J))) := by
  have h := overlap_graph_le_label P (disjointAND (I := I) (J := J))
  have he : pushMass (uniformMass (I → J → Bool)) disjointAND =
      productMass (fun _ : I => bernoulliMass (1 / (2 : ℝ) ^ Fintype.card J)) :=
    funext disjointAND_law
  rwa [he] at h

/-- Unused uniform seed coordinates and zero label coordinates permit arbitrary entropy. -/
def paddedAND {I J K L : Type*} [Fintype J]
    (x : (I → J → Bool) × (K → Bool)) : (I → Bool) × (L → Bool) :=
  (disjointAND x.1, fun _ => false)

theorem paddedAND_active_law {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L] (y : I → Bool) :
    pushMass (uniformMass ((I → J → Bool) × (K → Bool)))
      (Prod.fst ∘ (paddedAND (L := L))) y =
      productMass (fun _ : I => bernoulliMass (1 / (2 : ℝ) ^ Fintype.card J)) y := by
  change pushMass _ ((disjointAND (I := I) (J := J)) ∘ Prod.fst) y = _
  rw [uniformMass_unused_seed, disjointAND_law]

theorem overlap_paddedAND_graph_le {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (P : ((I → J → Bool) × (K → Bool)) × ((I → Bool) × (L → Bool)) → ℝ) :
    massOverlap P (graphLaw paddedAND) ≤
      massOverlap (pushMass P (Prod.fst ∘ Prod.snd))
        (productMass (fun _ : I => bernoulliMass (1 / (2 : ℝ) ^ Fintype.card J))) := by
  have h := overlap_graph_le_processed_labels P paddedAND Prod.fst
  have he : pushMass (uniformMass ((I → J → Bool) × (K → Bool)))
      (Prod.fst ∘ (paddedAND (L := L))) =
      productMass (fun _ : I => bernoulliMass (1 / (2 : ℝ) ^ Fintype.card J)) :=
    funext paddedAND_active_law
  rwa [he] at h

theorem paddedAND_support_card {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L] :
    Fintype.card {z // graphLaw (paddedAND (I := I) (J := J) (K := K) (L := L)) z ≠ 0} =
      2 ^ (Fintype.card I * Fintype.card J + Fintype.card K) := by
  rw [graphLaw_support_card]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool]
  rw [← pow_mul, Nat.mul_comm (Fintype.card J), ← pow_add]

def hierarchyBlocks (d N k : ℕ) : ℕ := min (k / (d+1)) (N-k)

theorem hierarchyBlocks_seed_bound (d N k : ℕ) :
    hierarchyBlocks d N k * (d+1) ≤ k := by
  exact (Nat.mul_le_mul_right (d+1) (min_le_left _ _)).trans
    (Nat.div_mul_le_self k (d+1))

theorem hierarchyBlocks_label_bound (d N k : ℕ) :
    hierarchyBlocks d N k ≤ N-k := min_le_right _ _

abbrev HierarchySeed (d N k : ℕ) :=
  (Fin (hierarchyBlocks d N k) → Fin (d+1) → Bool) ×
    (Fin (k-hierarchyBlocks d N k*(d+1)) → Bool)

abbrev HierarchyLabels (d N k : ℕ) :=
  (Fin (hierarchyBlocks d N k) → Bool) ×
    (Fin (N-k-hierarchyBlocks d N k) → Bool)

def hierarchyMap (d N k : ℕ) : HierarchySeed d N k → HierarchyLabels d N k := paddedAND

theorem hierarchySeed_card (d N k : ℕ) : Fintype.card (HierarchySeed d N k) = 2^k := by
  have h := hierarchyBlocks_seed_bound d N k
  simp only [HierarchySeed, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm (d+1), ← pow_add, Nat.add_sub_of_le h]

theorem hierarchyLabels_card (d N k : ℕ) :
    Fintype.card (HierarchyLabels d N k) = 2^(N-k) := by
  have h := hierarchyBlocks_label_bound d N k
  simp only [HierarchyLabels, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  rw [← pow_add, Nat.add_sub_of_le h]

/-- The specified graph distribution is flat on exactly `2^k` points. -/
theorem hierarchy_support_card (d N k : ℕ) :
    Fintype.card {z // graphLaw (hierarchyMap d N k) z ≠ 0} = 2^k := by
  rw [graphLaw_support_card, hierarchySeed_card]

theorem hierarchy_atom_mass (d N k : ℕ) (x : HierarchySeed d N k) :
    graphLaw (hierarchyMap d N k) (graphMap (hierarchyMap d N k) x) =
      1 / (2 : ℝ)^k := by
  change pushMass _ _ _ = _
  rw [pushMass_injective_at _ _ (graphMap_injective _)]
  change 1 / (Fintype.card (HierarchySeed d N k) : ℝ) = _
  rw [hierarchySeed_card, Nat.cast_pow, Nat.cast_ofNat]

theorem hierarchy_ambient_card (d N k : ℕ) (hk : k ≤ N) :
    Fintype.card (HierarchySeed d N k × HierarchyLabels d N k) = 2^N := by
  rw [Fintype.card_prod, hierarchySeed_card, hierarchyLabels_card, ← pow_add,
    Nat.add_sub_of_le hk]

/-- The number of active blocks is linear in the smaller of entropy and codimension. -/
theorem hierarchyBlocks_entropy_bound_nat (d N k : ℕ)
    (hs : 2*(d+1) ≤ min k (N-k)) :
    min k (N-k) ≤ 2*(d+1)*hierarchyBlocks d N k := by
  have hb : 0 < d+1 := Nat.succ_pos d
  have hk := min_le_left k (N-k)
  have hn := min_le_right k (N-k)
  unfold hierarchyBlocks
  by_cases h : k/(d+1) ≤ N-k
  · rw [min_eq_left h]
    have hdiv : 1 ≤ k/(d+1) := (Nat.one_le_div_iff hb).mpr (by omega)
    have hlt := Nat.lt_mul_div_succ k hb
    have hmul := Nat.mul_le_mul_left (d+1) hdiv
    nlinarith
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    nlinarith

theorem hierarchyBlocks_entropy_bound (d N k : ℕ)
    (hs : 2*(d+1) ≤ min k (N-k)) :
    ((min k (N-k) : ℕ) : ℝ) / (2*((d : ℝ)+1)) ≤ hierarchyBlocks d N k := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*((d : ℝ)+1))).mpr
  have h := hierarchyBlocks_entropy_bound_nat d N k hs
  have hr : ((min k (N-k) : ℕ) : ℝ) ≤ 2*((d : ℝ)+1)*(hierarchyBlocks d N k : ℝ) := by
    exact_mod_cast h
  nlinarith

/-- Evaluating the active products needs at most `k` field multiplications. -/
theorem hierarchy_multiplication_count (d N k : ℕ) :
    hierarchyBlocks d N k * d ≤ k := by
  exact (Nat.mul_le_mul_left _ (Nat.le_succ d)).trans (hierarchyBlocks_seed_bound d N k)

end SamplingLowerBounds.FlatGraph
