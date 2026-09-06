import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Finite information-theoretic calculations

The reference laws used in the paper are strictly positive. For that case
`finiteKL` is the usual finite Kullback--Leibler divergence, with the zero
terms interpreted using Lean's `Real.log 0 = 0` convention.

This file proves density domination implies a logarithmic KL bound and
aggregates coordinate test errors. Pinsker's inequality and KL tensorization
are NOT proved here: their numerical conclusions are explicit hypotheses of
`coordinate_test_sum_bound`.
-/

open scoped BigOperators

namespace SamplingLowerBounds.Information

noncomputable def finiteKL {A : Type*} [Fintype A] (R M : A → ℝ) : ℝ :=
  ∑ x, R x * Real.log (R x / M x)

/-- Gibbs' inequality for finite laws with a strictly positive reference. -/
theorem finiteKL_nonneg {A : Type*} [Fintype A]
    (R M : A → ℝ) (hR : ∀ x, 0 ≤ R x)
    (hmassR : ∑ x, R x = 1) (hmassM : ∑ x, M x = 1)
    (hM : ∀ x, 0 < M x) : 0 ≤ finiteKL R M := by
  have hpoint : ∀ x, R x - M x ≤ R x * Real.log (R x / M x) := by
    intro x
    by_cases hx : R x = 0
    · simpa only [hx, zero_sub, zero_mul] using neg_nonpos.mpr (hM x).le
    · have hxpos : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
      calc
        R x - M x = R x * (1 - (R x / M x)⁻¹) := by
          field_simp [hx, (hM x).ne']
        _ ≤ R x * Real.log (R x / M x) :=
          mul_le_mul_of_nonneg_left
            (Real.one_sub_inv_le_log_of_pos (div_pos hxpos (hM x))) (hR x)
  calc
    0 = ∑ x, (R x - M x) := by rw [Finset.sum_sub_distrib, hmassR, hmassM]; ring
    _ ≤ finiteKL R M := Finset.sum_le_sum fun x _ => hpoint x

/-- Pointwise density domination bounds relative entropy. -/
theorem finiteKL_le_log_of_domination {A : Type*} [Fintype A]
    (R M : A → ℝ) (C : ℝ)
    (hR : ∀ x, 0 ≤ R x) (hmass : ∑ x, R x = 1)
    (hM : ∀ x, 0 < M x) (_hC : 0 < C)
    (hdom : ∀ x, R x ≤ C * M x) :
    finiteKL R M ≤ Real.log C := by
  have hpoint : ∀ x, R x * Real.log (R x / M x) ≤ R x * Real.log C := by
    intro x
    by_cases hx : R x = 0
    · simp [hx]
    · have hxpos : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
      apply mul_le_mul_of_nonneg_left _ (hR x)
      exact Real.log_le_log (div_pos hxpos (hM x))
        ((div_le_iff₀ (hM x)).2 (hdom x))
  calc
    finiteKL R M ≤ ∑ x, R x * Real.log C :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = Real.log C := by rw [← Finset.sum_mul, hmass, one_mul]

/-- The normalization cost in the tilted-cube argument. -/
theorem finiteKL_le_log_inv {A : Type*} [Fintype A]
    (R M : A → ℝ) (Z : ℝ)
    (hR : ∀ x, 0 ≤ R x) (hmass : ∑ x, R x = 1)
    (hM : ∀ x, 0 < M x) (hZ : 0 < Z)
    (hdom : ∀ x, R x ≤ M x / Z) :
    finiteKL R M ≤ Real.log (1 / Z) := by
  apply finiteKL_le_log_of_domination R M (1 / Z) hR hmass hM (by positivity)
  intro x
  simpa [div_eq_mul_inv, mul_comm] using hdom x

/-- The weighted-cube normalizer bound gives the common information budget. -/
theorem log_inv_le_mul_log_inv {Z ω : ℝ} {K : ℕ}
    (hω : 0 < ω) (hnorm : ω ^ K ≤ Z) :
    Real.log (1 / Z) ≤ (K : ℝ) * Real.log (1 / ω) := by
  have hlog := Real.log_le_log (pow_pos hω K) hnorm
  rw [Real.log_pow] at hlog
  simpa only [one_div, Real.log_inv, mul_neg] using neg_le_neg hlog

/-- Combining tilted density domination and the weighted-cube normalizer
bound yields the whole-output KL budget in the paper. -/
theorem finiteKL_le_cube_budget {A : Type*} [Fintype A]
    (R M : A → ℝ) (Z ω : ℝ) (K : ℕ)
    (hR : ∀ x, 0 ≤ R x) (hmass : ∑ x, R x = 1)
    (hM : ∀ x, 0 < M x) (hω : 0 < ω) (hnorm : ω ^ K ≤ Z)
    (hdom : ∀ x, R x ≤ M x / Z) :
    finiteKL R M ≤ (K : ℝ) * Real.log (1 / ω) := by
  have hZ : 0 < Z := (pow_pos hω K).trans_le hnorm
  exact (finiteKL_le_log_inv R M Z hR hmass hM hZ hdom).trans
    (log_inv_le_mul_log_inv hω hnorm)

/-- Cauchy--Schwarz aggregation of coordinate errors after Pinsker and
tensorization have supplied the two stated inequalities. -/
theorem coordinate_test_sum_bound {I : Type*} [Fintype I]
    (e d : I → ℝ) (a D : ℝ)
    (ha : 0 ≤ a) (hd : ∀ i, 0 ≤ d i)
    (hbudget : ∑ i, d i ≤ D)
    (herror : ∀ i, |e i| ≤ a * Real.sqrt (d i / 2)) :
    |∑ i, e i| ≤ a * Real.sqrt ((Fintype.card I : ℝ) * D / 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : I => (1 : ℝ)) (fun i => Real.sqrt (d i / 2))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hcs
  have hsquares : (∑ i, (Real.sqrt (d i / 2)) ^ 2) = (∑ i, d i) / 2 := by
    have hsqeach (i : I) : (Real.sqrt (d i / 2)) ^ 2 = d i / 2 :=
      Real.sq_sqrt (div_nonneg (hd i) (by norm_num))
    simp_rw [hsqeach]
    exact (Finset.sum_div ..).symm
  rw [hsquares] at hcs
  have hsq : (∑ i, Real.sqrt (d i / 2)) ^ 2 ≤ (Fintype.card I : ℝ) * D / 2 := by
    calc
      _ ≤ (Fintype.card I : ℝ) * ((∑ i, d i) / 2) := hcs
      _ ≤ (Fintype.card I : ℝ) * (D / 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbudget (by norm_num))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  have hsqrt : (∑ i, Real.sqrt (d i / 2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) * D / 2) := by
    exact Real.le_sqrt_of_sq_le hsq
  calc
    |∑ i, e i| ≤ ∑ i, |e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, a * Real.sqrt (d i / 2) := Finset.sum_le_sum fun i _ => herror i
    _ = a * ∑ i, Real.sqrt (d i / 2) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt ha

end SamplingLowerBounds.Information
