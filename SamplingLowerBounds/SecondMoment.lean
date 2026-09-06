import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Finite second-moment aggregation

This file proves the algebraic/probabilistic aggregation step in the
paper's affine-cube argument. The information-theoretic estimates for
one- and two-vertex marginals are explicit hypotheses. No independence
of the tilted vertices is assumed or needed here.
-/

open scoped BigOperators

namespace SamplingLowerBounds
namespace SecondMoment

variable {Ω V I : Type*} [Fintype Ω] [Fintype V] [Fintype I]

/-- Expectation under a finite real-valued weight function. Probability
hypotheses are supplied only in the theorems that use them. -/
def expectation (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ ω * f ω

lemma expectation_const (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1) (c : ℝ) :
    expectation μ (fun _ => c) = c := by
  simp only [expectation, ← Finset.sum_mul, hμ, one_mul]

lemma expectation_mono (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    expectation μ f ≤ expectation μ g := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hμ ω)

lemma expectation_sum {J : Type*} [Fintype J]
    (μ : Ω → ℝ) (f : Ω → J → ℝ) :
    expectation μ (fun ω => ∑ j, f ω j) =
      ∑ j, expectation μ (fun ω => f ω j) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma expectation_div (μ : Ω → ℝ) (f : Ω → ℝ) (c : ℝ) :
    expectation μ (fun ω => f ω / c) = expectation μ f / c := by
  simp only [expectation, mul_div_assoc, Finset.sum_div]

/-- Squaring the centered average produces all ordered pairs, including
its diagonal. -/
lemma average_square [Nonempty V] (y : V → ℝ) (p : ℝ) :
    ((∑ v, y v) / (Fintype.card V : ℝ) - p) ^ 2 =
      (∑ v, ∑ w, (y v - p) * (y w - p)) /
        (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hK : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := V))
  have hcenter : (∑ v, y v) / (Fintype.card V : ℝ) - p =
      (∑ v, (y v - p)) / (Fintype.card V : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp [hK]
  rw [hcenter, div_pow]
  congr 1
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- A summed, centered two-vertex moment. -/
def moment (μ : Ω → ℝ) (Y : Ω → V → I → ℝ) (p : ℝ)
    (v w : V) : ℝ :=
  ∑ i, expectation μ (fun ω => (Y ω v i - p) * (Y ω w i - p))

/-- Finite expectation and coordinate summation commute with the exact
ordered-pair expansion of the squared average. -/
lemma expected_average_square [Nonempty V]
    (μ : Ω → ℝ) (Y : Ω → V → I → ℝ) (p : ℝ) :
    (∑ i, expectation μ (fun ω =>
      ((∑ v, Y ω v i) / (Fintype.card V : ℝ) - p) ^ 2)) =
      (∑ v, ∑ w, moment μ Y p v w) / (Fintype.card V : ℝ) ^ 2 := by
  classical
  simp_rw [average_square, expectation_div, expectation_sum]
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  rfl

/-- A matrix with diagonal at most `a + error` and off-diagonal at most
`error` has normalized total at most `a / |V| + error`. The error need
not be nonnegative for this algebraic fact. -/
lemma normalized_matrix_bound [Nonempty V] (A : V → V → ℝ)
    (a error : ℝ) (hdiag : ∀ v, A v v ≤ a + error)
    (hoff : ∀ v w, v ≠ w → A v w ≤ error) :
    (∑ v, ∑ w, A v w) / (Fintype.card V : ℝ) ^ 2 ≤
      a / (Fintype.card V : ℝ) + error := by
  classical
  have hK : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (Fintype.card_pos (α := V))
  have hentry : ∀ v w, A v w ≤ (if v = w then a else 0) + error := by
    intro v w
    by_cases h : v = w
    · subst w
      simpa using hdiag v
    · simpa [h] using hoff v w h
  have hsum : (∑ v, ∑ w, A v w) ≤
      (Fintype.card V : ℝ) * a + (Fintype.card V : ℝ) ^ 2 * error := by
    calc
      (∑ v, ∑ w, A v w) ≤
          ∑ v, ∑ w, ((if v = w then a else 0) + error) :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hentry v w
      _ = (Fintype.card V : ℝ) * a +
          (Fintype.card V : ℝ) ^ 2 * error := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
        ring
  apply (div_le_iff₀ (sq_pos_of_pos hK)).2
  calc
    (∑ v, ∑ w, A v w) ≤
        (Fintype.card V : ℝ) * a + (Fintype.card V : ℝ) ^ 2 * error := hsum
    _ = (a / (Fintype.card V : ℝ) + error) *
        (Fintype.card V : ℝ) ^ 2 := by
      field_simp [ne_of_gt hK]
      ring

/-- A pointwise lower bound on each coordinate mean's distance from `p`
lower-bounds the sum of their expected squared distances under any probability
measure, including a tilted cube law. -/
lemma bias_gap_lower_bound [Nonempty V]
    (μ : Ω → ℝ) (hμnonneg : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (Y : Ω → V → I → ℝ) (p δ : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ ω i,
      δ ≤ |(∑ v, Y ω v i) / (Fintype.card V : ℝ) - p|) :
    (Fintype.card I : ℝ) * δ ^ 2 ≤
      ∑ i, expectation μ (fun ω =>
        ((∑ v, Y ω v i) / (Fintype.card V : ℝ) - p) ^ 2) := by
  classical
  calc
    (Fintype.card I : ℝ) * δ ^ 2 = ∑ _i : I, δ ^ 2 := by simp
    _ ≤ ∑ i, expectation μ (fun ω =>
        ((∑ v, Y ω v i) / (Fintype.card V : ℝ) - p) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← expectation_const μ hμsum (δ ^ 2)]
      apply expectation_mono μ hμnonneg
      intro ω
      have hs := (sq_le_sq₀ hδ (abs_nonneg _)).2 (hgap ω i)
      simpa only [sq_abs] using hs

/-- The second-moment conclusion used by affine-cube amplification.
The inputs `hdiag` and `hoff` are exactly the one- and two-vertex moment
estimates supplied by the information-theoretic portion of the proof. -/
theorem bias_gap_second_moment_bound [Nonempty V]
    (μ : Ω → ℝ) (hμnonneg : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (Y : Ω → V → I → ℝ) (p δ variance error : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ ω i,
      δ ≤ |(∑ v, Y ω v i) / (Fintype.card V : ℝ) - p|)
    (hdiag : ∀ v, moment μ Y p v v ≤ (Fintype.card I : ℝ) * variance + error)
    (hoff : ∀ v w, v ≠ w → moment μ Y p v w ≤ error) :
    (Fintype.card I : ℝ) * δ ^ 2 ≤
      (Fintype.card I : ℝ) * variance / (Fintype.card V : ℝ) + error := by
  calc
    (Fintype.card I : ℝ) * δ ^ 2 ≤
        ∑ i, expectation μ (fun ω =>
          ((∑ v, Y ω v i) / (Fintype.card V : ℝ) - p) ^ 2) :=
      bias_gap_lower_bound μ hμnonneg hμsum Y p δ hδ hgap
    _ = (∑ v, ∑ w, moment μ Y p v w) / (Fintype.card V : ℝ) ^ 2 :=
      expected_average_square μ Y p
    _ ≤ (Fintype.card I : ℝ) * variance / (Fintype.card V : ℝ) + error :=
      normalized_matrix_bound (moment μ Y p) _ error hdiag hoff

end SecondMoment
end SamplingLowerBounds
