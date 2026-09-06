import SamplingLowerBounds.Tensorization

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.Information

noncomputable def pushMass {A B : Type*} [Fintype A]
    (R : A → ℝ) (f : A → B) (b : B) : ℝ :=
  ∑ x, if f x = b then R x else 0

theorem pushMass_nonneg {A B : Type*} [Fintype A]
    (R : A → ℝ) (f : A → B) (hR : ∀ x, 0 ≤ R x) (b : B) :
    0 ≤ pushMass R f b := by
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all

theorem pushMass_expectation {A B : Type*} [Fintype A] [Fintype B]
    (R : A → ℝ) (f : A → B) (g : B → ℝ) :
    ∑ b, pushMass R f b * g b = ∑ x, R x * g (f x) := by
  simp only [pushMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem pushMass_sum {A B : Type*} [Fintype A] [Fintype B]
    (R : A → ℝ) (f : A → B) : ∑ b, pushMass R f b = ∑ x, R x := by
  simpa using pushMass_expectation R f (fun _ => 1)

theorem le_pushMass {A B : Type*} [Fintype A]
    (R : A → ℝ) (f : A → B) (hR : ∀ x, 0 ≤ R x) (x : A) :
    R x ≤ pushMass R f (f x) := by
  unfold pushMass
  have := Finset.single_le_sum (s := Finset.univ)
    (f := fun y : A => if f y = f x then R y else 0)
    (fun y _ => by dsimp; split_ifs <;> simp_all) (Finset.mem_univ x)
  simpa using this

theorem pushMass_pos_of_surjective {A B : Type*} [Fintype A]
    (M : A → ℝ) (f : A → B) (hM : ∀ x, 0 < M x)
    (hf : Function.Surjective f) (b : B) : 0 < pushMass M f b := by
  obtain ⟨x,rfl⟩ := hf b
  exact (hM x).trans_le (le_pushMass M f (fun x => (hM x).le) x)

theorem finiteKL_data_processing {A B : Type*} [Fintype A] [Fintype B]
    (R M : A → ℝ) (f : A → B) (hR : ∀ x, 0 ≤ R x)
    (hRsum : ∑ x, R x = 1) (hM : ∀ x, 0 < M x)
    (hf : Function.Surjective f) :
    finiteKL (pushMass R f) (pushMass M f) ≤ finiteKL R M := by
  let T : A → ℝ := fun x => M x * (pushMass R f (f x) / pushMass M f (f x))
  have hpM := pushMass_pos_of_surjective M f hM hf
  have hpR := pushMass_nonneg R f hR
  have hT : ∀ x, 0 ≤ T x := by
    intro x
    exact mul_nonneg (hM x).le (div_nonneg (hpR _) (hpM _).le)
  have hTsum : ∑ x, T x = 1 := by
    have he := pushMass_expectation M f (fun b => pushMass R f b / pushMass M f b)
    dsimp [T]
    rw [← he]
    simp_rw [mul_div_cancel₀ _ (hpM _).ne']
    exact (pushMass_sum R f).trans hRsum
  have hTsupp : ∀ x, R x ≠ 0 → 0 < T x := by
    intro x hx
    have hr : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
    exact mul_pos (hM x) (div_pos (hr.trans_le (le_pushMass R f hR x)) (hpM _))
  have hpoint (x : A) : R x * Real.log (R x / M x) =
      R x * Real.log (R x / T x) +
        R x * Real.log (pushMass R f (f x) / pushMass M f (f x)) := by
    by_cases hx : R x = 0
    · simp [hx]
    have hr : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
    have hp : 0 < pushMass R f (f x) := hr.trans_le (le_pushMass R f hR x)
    rw [Real.log_div hx (hM x).ne', Real.log_div hx (hTsupp x hx).ne']
    dsimp [T]
    rw [Real.log_mul (hM x).ne' (div_pos hp (hpM _)).ne']
    ring
  have heq : finiteKL R M = finiteKL R T +
      finiteKL (pushMass R f) (pushMass M f) := by
    unfold finiteKL
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    congr 1
    exact (pushMass_expectation R f
      (fun b => Real.log (pushMass R f b / pushMass M f b))).symm
  have hn := finiteKL_nonneg_of_support R T hR hT hRsum hTsum hTsupp
  rw [heq]
  linarith

end SamplingLowerBounds.Information
