import SamplingLowerBounds.BinaryPinsker
import SamplingLowerBounds.DataProcessing

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.Information

theorem finite_pinsker {A : Type*} [Fintype A]
    (R M : A → ℝ) (hR : ∀ x, 0 ≤ R x) (hM : ∀ x, 0 < M x)
    (hRsum : ∑ x, R x = 1) (hMsum : ∑ x, M x = 1) :
    (∑ x, |R x - M x|)^2 ≤ 2 * finiteKL R M := by
  let f : A → Bool := fun x => decide (M x ≤ R x)
  let q := pushMass R f true
  let p := pushMass M f true
  have heq : ∑ x, |R x-M x| = 2*(q-p) := by
    have hpoint (x : A) : |R x-M x| =
        2*((if f x = true then R x else 0) - (if f x = true then M x else 0)) -
          (R x-M x) := by
      by_cases hx : M x ≤ R x
      · simp [f,hx,abs_of_nonneg (sub_nonneg.mpr hx)]; ring
      · simp [f,hx,abs_of_neg (sub_neg.mpr (lt_of_not_ge hx))]
    simp_rw [hpoint]
    simp only [Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.mul_sum,
      hRsum, hMsum, sub_self, sub_zero]
    simp only [q, p, pushMass]
    congr 2 <;> apply Finset.sum_congr rfl <;> intro x _ <;> split_ifs <;> rfl
  have hnonneg := finiteKL_nonneg R M hR hRsum hMsum hM
  by_cases ht : ∃ x, f x = true
  · by_cases hf : ∃ x, f x = false
    · have hsurj : Function.Surjective f := by
        intro b
        cases b
        · exact hf
        · exact ht
      have hpos := pushMass_pos_of_surjective M f hM hsurj
      have hrpos := pushMass_nonneg R f hR
      have hrsum := (pushMass_sum R f).trans hRsum
      have hmsum := (pushMass_sum M f).trans hMsum
      simp only [Fintype.sum_bool] at hrsum hmsum
      have hq0 : 0 ≤ q := hrpos true
      have hq1 : q ≤ 1 := by dsimp [q]; linarith [hrpos false]
      have hp0 : 0 < p := hpos true
      have hp1 : p < 1 := by dsimp [p]; linarith [hpos false]
      have hrf : pushMass R f false = 1-q := by dsimp [q]; linarith
      have hmf : pushMass M f false = 1-p := by dsimp [p]; linarith
      have hkl : finiteKL (pushMass R f) (pushMass M f) = binaryKL q p := by
        simp only [finiteKL, Fintype.sum_bool, hrf, hmf, binaryKL]
        dsimp [q,p]
      have hb := binary_pinsker q p hq0 hq1 hp0 hp1
      have hd := finiteKL_data_processing R M f hR hRsum hM hsurj
      rw [hkl] at hd
      rw [heq]
      nlinarith
    · have hall : ∀ x, f x = true := by
        intro x
        cases hx : f x
        · exact False.elim (hf ⟨x,hx⟩)
        · rfl
      have hq : q = 1 := by simpa [q, pushMass, hall] using hRsum
      have hp : p = 1 := by simpa [p, pushMass, hall] using hMsum
      rw [heq,hq,hp]; nlinarith
  · have hall : ∀ x, f x ≠ true := by simpa using ht
    have hq : q = 0 := by simp [q, pushMass, hall]
    have hp : p = 0 := by simp [p, pushMass, hall]
    rw [heq,hq,hp]; nlinarith

theorem finite_coordinate_test {A : Type*} [Fintype A]
    (R M : A → ℝ) (hR : ∀ x, 0 ≤ R x) (hM : ∀ x, 0 < M x)
    (hRsum : ∑ x, R x = 1) (hMsum : ∑ x, M x = 1)
    (g : A → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (hg : ∀ x, |g x-c| ≤ a/2) :
    |(∑ x, R x*g x) - ∑ x, M x*g x| ≤ a * Real.sqrt (finiteKL R M / 2) := by
  have hcenter : (∑ x, R x*g x) - ∑ x, M x*g x =
      ∑ x, (R x-M x)*(g x-c) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hRsum, hMsum]
    ring
  have hbound : |∑ x, (R x-M x)*(g x-c)| ≤ (∑ x, |R x-M x|)*(a/2) := by
    calc
      _ ≤ ∑ x, |(R x-M x)*(g x-c)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |R x-M x| * (a/2) := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hg x) (abs_nonneg _)
      _ = _ := (Finset.sum_mul ..).symm
  have hk := finiteKL_nonneg R M hR hRsum hMsum hM
  have hp := finite_pinsker R M hR hM hRsum hMsum
  have hs : (∑ x, |R x-M x|) ≤ 2 * Real.sqrt (finiteKL R M / 2) := by
    have hsq := Real.sq_sqrt (div_nonneg hk (by norm_num : (0:ℝ) ≤ 2))
    have hsn := Real.sqrt_nonneg (finiteKL R M / 2)
    nlinarith [sq_nonneg ((∑ x, |R x-M x|) - 2*Real.sqrt (finiteKL R M/2))]
  rw [hcenter]
  calc
    _ ≤ (∑ x, |R x-M x|)*(a/2) := hbound
    _ ≤ (2 * Real.sqrt (finiteKL R M/2))*(a/2) :=
      mul_le_mul_of_nonneg_right hs (div_nonneg ha (by norm_num))
    _ = _ := by ring

end SamplingLowerBounds.Information
