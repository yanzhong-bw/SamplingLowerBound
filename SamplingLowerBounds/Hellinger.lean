import SamplingLowerBounds.Tensorization
import Mathlib.Data.Real.Sqrt

/-!
# Finite Hellinger affinity and overlap

These bounds apply to actual finite nonnegative mass functions. The overlap
is the sum of pointwise minima, matching the common mass used by `CubeTilt`.
No information-theoretic inequality is assumed as an input.
-/

open scoped BigOperators

namespace SamplingLowerBounds.Information

open Classical

/-- The Bhattacharyya coefficient, also called Hellinger affinity. -/
noncomputable def bhattacharyyaCoeff {A : Type*} [Fintype A]
    (P M : A → ℝ) : ℝ := ∑ a, Real.sqrt (P a * M a)

theorem bhattacharyyaCoeff_nonneg {A : Type*} [Fintype A]
    (P M : A → ℝ) : 0 ≤ bhattacharyyaCoeff P M :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- The sharp overlap-to-affinity inequality for two probability laws. -/
theorem bhattacharyyaCoeff_sq_le_overlap {A : Type*} [Fintype A]
    (P M : A → ℝ) (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a)
    (hPsum : ∑ a, P a = 1) (hMsum : ∑ a, M a = 1) :
    bhattacharyyaCoeff P M ^ 2 ≤
      (∑ a, min (P a) (M a)) * (2 - ∑ a, min (P a) (M a)) := by
  have hmax : (∑ a, max (P a) (M a)) = 2 - ∑ a, min (P a) (M a) := by
    have hsum : (∑ a, min (P a) (M a)) + (∑ a, max (P a) (M a)) = 2 := by
      rw [← Finset.sum_add_distrib]
      simp only [min_add_max, Finset.sum_add_distrib, hPsum, hMsum]
      norm_num
    linarith
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (R := ℝ) Finset.univ
    (r := fun a => Real.sqrt (P a * M a))
    (f := fun a => min (P a) (M a)) (g := fun a => max (P a) (M a))
    (fun a _ => le_min (hP a) (hM a))
    (fun a _ => (hP a).trans (le_max_left _ _))
    (fun a _ => by
      dsimp only
      rw [Real.sq_sqrt (mul_nonneg (hP a) (hM a))]
      rcases le_total (P a) (M a) with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h, mul_comm])
  simpa only [bhattacharyyaCoeff, hmax] using h

/-- Exponentially small overlap implies exponentially small affinity. -/
theorem bhattacharyyaCoeff_sq_le_twice_overlap {A : Type*} [Fintype A]
    (P M : A → ℝ) (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a)
    (hPsum : ∑ a, P a = 1) (hMsum : ∑ a, M a = 1) :
    bhattacharyyaCoeff P M ^ 2 ≤ 2 * ∑ a, min (P a) (M a) := by
  have h := bhattacharyyaCoeff_sq_le_overlap P M hP hM hPsum hMsum
  nlinarith [sq_nonneg (∑ a, min (P a) (M a))]

theorem bhattacharyyaCoeff_le_one {A : Type*} [Fintype A]
    (P M : A → ℝ) (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a)
    (hPsum : ∑ a, P a = 1) (hMsum : ∑ a, M a = 1) :
    bhattacharyyaCoeff P M ≤ 1 := by
  have h := bhattacharyyaCoeff_sq_le_overlap P M hP hM hPsum hMsum
  nlinarith [sq_nonneg ((∑ a, min (P a) (M a)) - 1)]

/-- Square roots commute with products of nonnegative real factors. -/
theorem sqrt_prod_nonneg {I : Type*} (s : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Real.sqrt_mul (hf i (Finset.mem_insert_self i s)),
      Finset.prod_insert hi, ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- Hellinger affinity is multiplicative for arbitrary finite product laws. -/
theorem bhattacharyyaCoeff_productMass {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]
    (P M : I → A → ℝ) (hP : ∀ i a, 0 ≤ P i a) (hM : ∀ i a, 0 ≤ M i a) :
    bhattacharyyaCoeff (productMass P) (productMass M) =
      ∏ i, bhattacharyyaCoeff (P i) (M i) := by
  simp only [bhattacharyyaCoeff, productMass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.prod_mul_distrib]
  exact sqrt_prod_nonneg Finset.univ (fun i => P i (x i) * M i (x i))
    (fun i _ => mul_nonneg (hP i (x i)) (hM i (x i)))

/-- Tensor powers remove the constant prefactor in the affinity bound.

The argument uses the Archimedean unboundedness of powers of a real number
strictly larger than one; the conclusion is not a supplied analytic premise.
-/
theorem tensor_power_remove_prefactor (b a : ℝ)
    (h : ∀ m : ℕ, 1 ≤ m → b ^ (2 * m) ≤ 2 * Real.exp (-a * (m : ℝ))) :
    b ≤ Real.exp (-a / 2) := by
  by_contra hnot
  have hb : Real.exp (-a / 2) < b := lt_of_not_ge hnot
  have he : 0 < Real.exp (-a / 2) := Real.exp_pos _
  have hsquare : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hratio : 1 < b ^ 2 / Real.exp (-a) := by
    apply (lt_div_iff₀ (Real.exp_pos _)).mpr
    rw [one_mul, ← hsquare]
    nlinarith
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 : ℝ) hratio
  have hmpos : 1 ≤ m := by
    by_contra hmnot
    have hmzero : m = 0 := by omega
    simp [hmzero] at hm
  have hexp : Real.exp (-a * (m : ℝ)) = Real.exp (-a) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp : (b ^ 2 / Real.exp (-a)) ^ m ≤ 2 := by
    rw [div_pow, ← pow_mul]
    apply (div_le_iff₀ (pow_pos (Real.exp_pos _) m)).mpr
    simpa only [hexp] using h m hmpos
  exact (not_lt_of_ge hp) hm

end SamplingLowerBounds.Information
