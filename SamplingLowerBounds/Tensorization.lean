import SamplingLowerBounds.FiniteInformation
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace SamplingLowerBounds.Information

open Classical

theorem finiteKL_nonneg_of_support {A : Type*} [Fintype A]
    (R M : A → ℝ) (hR : ∀ x, 0 ≤ R x) (hM : ∀ x, 0 ≤ M x)
    (hRsum : ∑ x, R x = 1) (hMsum : ∑ x, M x = 1)
    (hsupport : ∀ x, R x ≠ 0 → 0 < M x) : 0 ≤ finiteKL R M := by
  have hp : ∀ x, R x - M x ≤ R x * Real.log (R x / M x) := by
    intro x
    by_cases hx : R x = 0
    · simpa [hx] using neg_nonpos.mpr (hM x)
    · have hr : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
      have hm := hsupport x hx
      calc
        R x - M x = R x * (1 - (R x / M x)⁻¹) := by
          field_simp [hx, hm.ne']
        _ ≤ R x * Real.log (R x / M x) :=
          mul_le_mul_of_nonneg_left
            (Real.one_sub_inv_le_log_of_pos (div_pos hr hm)) (hR x)
  calc
    0 = ∑ x, (R x - M x) := by rw [Finset.sum_sub_distrib, hRsum, hMsum]; ring
    _ ≤ finiteKL R M := Finset.sum_le_sum fun x _ => hp x

noncomputable def marginal {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (i : I) (a : A) : ℝ := by
  classical
  exact ∑ x, if x i = a then R x else 0

theorem marginal_nonneg {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (hR : ∀ x, 0 ≤ R x) (i : I) (a : A) :
    0 ≤ marginal R i a := by
  classical
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all

theorem marginal_expectation {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (i : I) (g : A → ℝ) :
    ∑ a, marginal R i a * g a = ∑ x, R x * g (x i) := by
  classical
  simp only [marginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem marginal_sum {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (hRsum : ∑ x, R x = 1) (i : I) :
    ∑ a, marginal R i a = 1 := by
  simpa using (marginal_expectation R i (fun _ => 1)).trans (by simpa using hRsum)

theorem le_marginal {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (hR : ∀ x, 0 ≤ R x) (x : I → A) (i : I) :
    R x ≤ marginal R i (x i) := by
  classical
  unfold marginal
  have := Finset.single_le_sum (s := Finset.univ)
    (f := fun y : I → A => if y i = x i then R y else 0)
    (fun y _ => by dsimp; split_ifs <;> simp_all) (Finset.mem_univ x)
  simpa using this

noncomputable def productMass {I A : Type*} [Fintype I]
    (M : I → A → ℝ) (x : I → A) : ℝ := ∏ i, M i (x i)

theorem productMass_sum {I A : Type*} [Fintype I] [Fintype A]
    (M : I → A → ℝ) (hM : ∀ i, ∑ a, M i a = 1) :
    ∑ x, productMass M x = 1 := by
  classical
  simpa [productMass, hM] using (Fintype.prod_sum M).symm

theorem finiteKL_product_decomposition {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (M : I → A → ℝ)
    (hR : ∀ x, 0 ≤ R x) (hM : ∀ i a, 0 < M i a) :
    finiteKL R (productMass M) =
      finiteKL R (productMass (marginal R)) + ∑ i, finiteKL (marginal R i) (M i) := by
  classical
  have hpoint (x : I → A) :
      R x * Real.log (R x / productMass M x) =
        R x * Real.log (R x / productMass (marginal R) x) +
          ∑ i, R x * Real.log (marginal R i (x i) / M i (x i)) := by
    by_cases hx : R x = 0
    · simp [hx]
    have hr : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
    have hmarg (i : I) : 0 < marginal R i (x i) := hr.trans_le (le_marginal R hR x i)
    have hpM : productMass M x ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hM i (x i)).ne'
    have hpR : productMass (marginal R) x ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => (hmarg i).ne'
    rw [Real.log_div hx hpM, Real.log_div hx hpR]
    simp only [productMass, Real.log_prod _ _ (fun i _ => (hM i (x i)).ne'),
      Real.log_prod _ _ (fun i _ => (hmarg i).ne')]
    simp only [Real.log_div (hmarg _).ne' (hM _ _).ne']
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  unfold finiteKL
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (marginal_expectation R i (fun a => Real.log (marginal R i a / M i a))).symm

theorem finiteKL_tensorization {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (M : I → A → ℝ)
    (hR : ∀ x, 0 ≤ R x) (hRsum : ∑ x, R x = 1)
    (hM : ∀ i a, 0 < M i a) :
    ∑ i, finiteKL (marginal R i) (M i) ≤ finiteKL R (productMass M) := by
  classical
  have hprod : ∀ x, 0 ≤ productMass (marginal R) x :=
    fun x => Finset.prod_nonneg fun i _ => marginal_nonneg R hR i (x i)
  have hsupport : ∀ x, R x ≠ 0 → 0 < productMass (marginal R) x := by
    intro x hx
    have hr : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
    exact Finset.prod_pos fun i _ => hr.trans_le (le_marginal R hR x i)
  have hkl := finiteKL_nonneg_of_support R (productMass (marginal R)) hR hprod hRsum
    (productMass_sum (marginal R) (marginal_sum R hRsum)) hsupport
  rw [finiteKL_product_decomposition R M hR hM]
  linarith

end SamplingLowerBounds.Information
