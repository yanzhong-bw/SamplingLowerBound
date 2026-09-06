import SamplingLowerBounds.Cube
import SamplingLowerBounds.AffinePair
import SamplingLowerBounds.Tilt
import SamplingLowerBounds.FiniteInformation

/-!
# The actual overlap-induced tilted affine-cube law

This module connects the combinatorial cube theorems to the finite
change-of-measure calculation. The seed law is uniform, `outputLaw Q` is its
pushforward, the retention weight is constructed from its overlap with `M`, and
the normalizing constant is the actual affine-cube expectation. Pairwise
independence and the lower bound on that normalizer are proved, not hypotheses.
-/

open scoped BigOperators

namespace SamplingLowerBounds.CubeTilt

/-- Uniform real-valued mass function on a finite type. -/
noncomputable def uniformMass (Ω : Type*) [Fintype Ω] : Ω → ℝ :=
  fun _ => 1 / (Fintype.card Ω : ℝ)

lemma uniformMass_nonneg (Ω : Type*) [Fintype Ω] (x : Ω) :
    0 ≤ uniformMass Ω x := by
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

lemma uniformMass_pos (Ω : Type*) [Fintype Ω] [Nonempty Ω] (x : Ω) :
    0 < uniformMass Ω x := by
  exact div_pos zero_lt_one (Nat.cast_pos.mpr Fintype.card_pos)

lemma uniformMass_sum (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    (∑ x, uniformMass Ω x) = 1 := by
  simp [uniformMass, Fintype.card_ne_zero]

lemma uniform_normalizer {Ω : Type*} [Fintype Ω] (W : Ω → ℝ) :
    tiltNormalizer (uniformMass Ω) W = 𝔼 x, W x := by
  simp only [tiltNormalizer, Fintype.expect_eq_sum_div_card, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  simp [uniformMass, div_eq_mul_inv, mul_comm]

lemma uniform_event {Ω : Type*} [Fintype Ω] (E : Ω → Prop) [DecidablePred E] :
    finiteEventMass (uniformMass Ω) E = 𝔼 x, if E x then (1 : ℝ) else 0 := by
  classical
  simp only [finiteEventMass, Fintype.expect_eq_sum_div_card, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx, uniformMass]

variable {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A]

/-- Output distribution of a map on the uniform seed. -/
noncomputable def outputLaw (Q : G → A) (a : A) : ℝ :=
  finiteEventMass (uniformMass G) (fun x => Q x = a)

omit [AddCommGroup G] [Fintype A] in
lemma outputLaw_nonneg (Q : G → A) (a : A) : 0 ≤ outputLaw Q a :=
  finiteEventMass_nonneg _ _ (uniformMass_nonneg G)

lemma outputLaw_sum (Q : G → A) : (∑ a, outputLaw Q a) = 1 := by
  unfold outputLaw
  rw [finiteEventMass_sum_fibres]
  exact uniformMass_sum G

omit [Fintype A] in
lemma outputLaw_pos_on_image (Q : G → A) (x : G) : 0 < outputLaw Q (Q x) := by
  classical
  unfold outputLaw finiteEventMass
  apply Finset.sum_pos'
  · intro z _
    by_cases hz : Q z = Q x
    · simpa only [if_pos hz] using uniformMass_nonneg G z
    · simp only [if_neg hz, le_refl]
  · exact ⟨x, Finset.mem_univ x, by simpa using uniformMass_pos G x⟩

/-- The overlap of the actual source output law and the target mass function. -/
noncomputable def overlap (Q : G → A) (M : A → ℝ) : ℝ :=
  ∑ a, min (outputLaw Q a) (M a)

lemma overlap_pos (Q : G → A) (M : A → ℝ) (hM : ∀ a, 0 < M a) :
    0 < overlap Q M := by
  apply Finset.sum_pos'
  · intro a _
    exact le_min (outputLaw_nonneg Q a) (hM a).le
  · exact ⟨Q 0, Finset.mem_univ _, lt_min (outputLaw_pos_on_image Q 0) (hM _)⟩

lemma overlap_le_one (Q : G → A) (M : A → ℝ) : overlap Q M ≤ 1 := by
  calc
    overlap Q M ≤ ∑ a, outputLaw Q a := Finset.sum_le_sum (fun a _ => min_le_left _ _)
    _ = 1 := outputLaw_sum Q

/-- The seed retention weight used to construct the change of measure. -/
noncomputable def retention (Q : G → A) (M : A → ℝ) (x : G) : ℝ :=
  overlapRetention (outputLaw Q) M (Q x)

omit [AddCommGroup G] [Fintype A] in
lemma retention_nonneg (Q : G → A) (M : A → ℝ) (hM : ∀ a, 0 ≤ M a) (x : G) :
    0 ≤ retention Q M x :=
  overlapRetention_nonneg _ _ (outputLaw_nonneg Q) hM _

omit [AddCommGroup G] [Fintype A] in
lemma retention_le_one (Q : G → A) (M : A → ℝ) (x : G) :
    retention Q M x ≤ 1 :=
  overlapRetention_le_one _ _ (outputLaw_nonneg Q) _

omit [AddCommGroup G] in
lemma retention_expectation (Q : G → A) (M : A → ℝ) (hM : ∀ a, 0 ≤ M a) :
    (𝔼 x, retention Q M x) = overlap Q M := by
  rw [← uniform_normalizer]
  exact overlapRetention_expectation (uniformMass G) Q (outputLaw Q) M
    (outputLaw_nonneg Q) hM (fun _ => rfl)

/-- Cube parameters consist of all directions and the base point. -/
abbrev Parameters (G : Type*) (t : ℕ) := Cube.Tuple G t × G

/-- Output at a labelled vertex of the parametrized cube. -/
def vertexOutput (t : ℕ) (Q : G → A) (v : Cube.Tuple Bool t)
    (z : Parameters G t) : A := Q (Cube.vertex t z.1 z.2 v)

/-- The full product weight on the parameter space. -/
noncomputable def parameterWeight (t : ℕ) (Q : G → A) (M : A → ℝ)
    (z : Parameters G t) : ℝ :=
  ∏ v, overlapRetention (outputLaw Q) M (vertexOutput t Q v z)

/-- The actual normalizing constant, not an independently supplied budget. -/
noncomputable def normalizer (t : ℕ) (Q : G → A) (M : A → ℝ) : ℝ :=
  Cube.meanWeight t (retention Q M)

omit [Fintype A] in
lemma parameter_normalizer (t : ℕ) (Q : G → A) (M : A → ℝ) :
    tiltNormalizer (uniformMass (Parameters G t)) (parameterWeight t Q M) =
      normalizer t Q M := by
  rw [uniform_normalizer]
  change (𝔼 z : Cube.Tuple G t × G,
    Cube.weight t (retention Q M) z.1 z.2) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  rfl

/-- The normalization lower bound uses the actual source-target overlap. -/
theorem overlap_pow_le_normalizer (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) : overlap Q M ^ (2 ^ t) ≤ normalizer t Q M := by
  have h := Cube.weighted_affine_cube_lower_bound t (retention Q M)
    (retention_nonneg Q M hM)
  rw [retention_expectation Q M hM] at h
  exact h

lemma normalizer_pos (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hω : 0 < overlap Q M) : 0 < normalizer t Q M :=
  (pow_pos hω _).trans_le (overlap_pow_le_normalizer t Q M hM)

omit [Fintype A] in
lemma normalizer_le_one (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) : normalizer t Q M ≤ 1 :=
  Cube.meanWeight_le_one t _ (retention_nonneg Q M hM) (retention_le_one Q M)

/-- The normalized overlap-induced probability law on affine-cube parameters. -/
noncomputable def law (t : ℕ) (Q : G → A) (M : A → ℝ) : Parameters G t → ℝ :=
  finiteTilt (uniformMass (Parameters G t)) (parameterWeight t Q M) (normalizer t Q M)

lemma law_nonneg (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hω : 0 < overlap Q M) (z : Parameters G t) :
    0 ≤ law t Q M z := by
  apply finiteTilt_nonneg _ _ (uniformMass_nonneg _) _ (normalizer_pos t Q M hM hω)
  intro z
  apply Finset.prod_nonneg
  intro v _
  exact overlapRetention_nonneg _ _ (outputLaw_nonneg Q) hM _

lemma law_sum (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hω : 0 < overlap Q M) : (∑ z, law t Q M z) = 1 := by
  unfold law
  rw [← parameter_normalizer]
  exact finiteTilt_sum_eq_one _ _ (by rw [parameter_normalizer]; exact normalizer_pos t Q M hM hω)

omit [Fintype A] in
lemma uniform_vertex_law (t : ℕ) (Q : G → A) (v : Cube.Tuple Bool t) (a : A) :
    finiteEventMass (uniformMass (Parameters G t)) (fun z => vertexOutput t Q v z = a) =
      outputLaw Q a := by
  classical
  rw [uniform_event]
  change (𝔼 z : Cube.Tuple G t × G,
    if Q (Cube.vertex t z.1 z.2 v) = a then (1 : ℝ) else 0) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  rw [AffinePair.cube_single_expect t v (fun x => if Q x = a then (1 : ℝ) else 0)]
  exact (uniform_event (fun x => Q x = a)).symm

omit [Fintype A] in
lemma uniform_pair_law (t : ℕ) (Q : G → A)
    (v w : Cube.Tuple Bool t) (hvw : v ≠ w) (a b : A) :
    finiteEventMass (uniformMass (Parameters G t))
      (fun z => vertexOutput t Q v z = a ∧ vertexOutput t Q w z = b) =
      outputLaw Q a * outputLaw Q b := by
  classical
  rw [uniform_event]
  change (𝔼 z : Cube.Tuple G t × G,
    if Q (Cube.vertex t z.1 z.2 v) = a ∧ Q (Cube.vertex t z.1 z.2 w) = b
      then (1 : ℝ) else 0) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  rw [AffinePair.cube_pair_events t v w hvw (fun x => Q x = a) (fun x => Q x = b)]
  rw [← uniform_event, ← uniform_event]
  rfl

/-- The tilted one-vertex output distribution. -/
noncomputable def singleLaw (t : ℕ) (Q : G → A) (M : A → ℝ)
    (v : Cube.Tuple Bool t) (a : A) : ℝ :=
  finiteEventMass (law t Q M) (fun z => vertexOutput t Q v z = a)

/-- The tilted joint output distribution at two labelled vertices. -/
noncomputable def pairLaw (t : ℕ) (Q : G → A) (M : A → ℝ)
    (v w : Cube.Tuple Bool t) (ab : A × A) : ℝ :=
  finiteEventMass (law t Q M)
    (fun z => vertexOutput t Q v z = ab.1 ∧ vertexOutput t Q w z = ab.2)

/-- Actual affine-cube single-marginal domination, with no marginal-law hypothesis. -/
theorem single_domination (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hω : 0 < overlap Q M)
    (v : Cube.Tuple Bool t) (a : A) :
    singleLaw t Q M v a ≤ M a / normalizer t Q M := by
  exact overlap_tilt_single_domination (uniformMass (Parameters G t))
    (vertexOutput t Q) (outputLaw Q) M (uniformMass_nonneg _)
    (normalizer_pos t Q M hM hω) (outputLaw_nonneg Q) hM v a
    (uniform_vertex_law t Q v a)

/-- Actual affine-cube pair-marginal domination. The untilted independence
identity and the validity of the normalizer have already been discharged. -/
theorem pair_domination (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hω : 0 < overlap Q M)
    (v w : Cube.Tuple Bool t) (hvw : v ≠ w) (a b : A) :
    pairLaw t Q M v w (a,b) ≤ M a * M b / normalizer t Q M := by
  exact overlap_tilt_pair_domination (uniformMass (Parameters G t))
    (vertexOutput t Q) (outputLaw Q) M (uniformMass_nonneg _)
    (normalizer_pos t Q M hM hω) (outputLaw_nonneg Q) hM v w hvw a b
    (uniform_pair_law t Q v w hvw a b)

lemma singleLaw_sum (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hω : 0 < overlap Q M) (v : Cube.Tuple Bool t) :
    (∑ a, singleLaw t Q M v a) = 1 := by
  unfold singleLaw
  rw [finiteEventMass_sum_fibres]
  exact law_sum t Q M hM hω

lemma pairLaw_sum (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hω : 0 < overlap Q M) (v w : Cube.Tuple Bool t) :
    (∑ ab, pairLaw t Q M v w ab) = 1 := by
  change (∑ ab : A × A, finiteEventMass (law t Q M)
    (fun z => vertexOutput t Q v z = ab.1 ∧ vertexOutput t Q w z = ab.2)) = 1
  rw [Fintype.sum_prod_type]
  rw [finiteEventMass_sum_pair_fibres]
  exact law_sum t Q M hM hω

/-- The actual whole-output single-marginal KL budget in the paper. -/
theorem single_KL_budget (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 < M a) (hω : 0 < overlap Q M) (v : Cube.Tuple Bool t) :
    Information.finiteKL (singleLaw t Q M v) M ≤
      ((2 ^ t : ℕ) : ℝ) * Real.log (1 / overlap Q M) := by
  apply Information.finiteKL_le_cube_budget _ _ (normalizer t Q M) (overlap Q M) (2 ^ t)
    (fun a => finiteEventMass_nonneg _ _ (law_nonneg t Q M (fun a => (hM a).le) hω))
    (singleLaw_sum t Q M (fun a => (hM a).le) hω v) hM hω
    (overlap_pow_le_normalizer t Q M (fun a => (hM a).le))
  exact single_domination t Q M (fun a => (hM a).le) hω v

/-- The actual whole-output pair-marginal KL budget: all cube normalization,
independence, retention, and density-domination steps are included. -/
theorem pair_KL_budget (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 < M a) (hω : 0 < overlap Q M)
    (v w : Cube.Tuple Bool t) (hvw : v ≠ w) :
    Information.finiteKL (pairLaw t Q M v w) (fun ab => M ab.1 * M ab.2) ≤
      ((2 ^ t : ℕ) : ℝ) * Real.log (1 / overlap Q M) := by
  apply Information.finiteKL_le_cube_budget _ _ (normalizer t Q M) (overlap Q M) (2 ^ t)
    (fun ab => finiteEventMass_nonneg _ _ (law_nonneg t Q M (fun a => (hM a).le) hω))
    (pairLaw_sum t Q M (fun a => (hM a).le) hω v w)
    (fun ab => mul_pos (hM ab.1) (hM ab.2)) hω
    (overlap_pow_le_normalizer t Q M (fun a => (hM a).le))
  intro ab
  exact pair_domination t Q M (fun a => (hM a).le) hω v w hvw ab.1 ab.2

/-- With a positive target, positive overlap is automatic. Thus this joint
statement has only the finite seed map, target positivity and distinct labels
as inputs; every normalization and information estimate is proved internally. -/
theorem information_budgets (t : ℕ) (Q : G → A) (M : A → ℝ)
    (hM : ∀ a, 0 < M a) (v w : Cube.Tuple Bool t) (hvw : v ≠ w) :
    Information.finiteKL (singleLaw t Q M v) M ≤
        ((2 ^ t : ℕ) : ℝ) * Real.log (1 / overlap Q M) ∧
    Information.finiteKL (pairLaw t Q M v w) (fun ab => M ab.1 * M ab.2) ≤
        ((2 ^ t : ℕ) : ℝ) * Real.log (1 / overlap Q M) :=
  ⟨single_KL_budget t Q M hM (overlap_pos Q M hM) v,
    pair_KL_budget t Q M hM (overlap_pos Q M hM) v w hvw⟩

end SamplingLowerBounds.CubeTilt
