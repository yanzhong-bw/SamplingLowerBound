import SamplingLowerBounds.PolynomialModel
import Mathlib.Tactic.Ring

/-!
# Minimum nonzero weight of Boolean polynomial functions

The underlying polynomial need not be multilinear: the assertion concerns its
evaluated function, which may vanish identically even for a nonzero polynomial.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.PolynomialModel
noncomputable section

/-- Fix the first variable to a field element. -/
def slice {n : ℕ} (p : Polynomial (Fin (n + 1))) (b : F₂) : Polynomial (Fin n) :=
  MvPolynomial.eval₂ MvPolynomial.C (Fin.cases (MvPolynomial.C b) MvPolynomial.X) p

theorem slice_degree {n : ℕ} (p : Polynomial (Fin (n + 1))) (b : F₂) :
    (slice p b).totalDegree ≤ p.totalDegree := by
  apply totalDegree_affine_substitution
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

theorem eval_slice {n : ℕ} (p : Polynomial (Fin (n + 1))) (b : F₂)
    (x : Fin n → F₂) :
    MvPolynomial.eval x (slice p b) = MvPolynomial.eval (Fin.cons b x) p := by
  rw [slice, ← MvPolynomial.eval_assoc]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The finite difference between the two slices. Exponents of the first
variable disappear, and its positive degree is removed from every term. -/
def sliceDifference {n : ℕ} (p : Polynomial (Fin (n + 1))) : Polynomial (Fin n) :=
  ∑ m ∈ p.support,
    if m 0 = 0 then 0 else
      MvPolynomial.C (MvPolynomial.coeff m p) * ∏ j : Fin n, MvPolynomial.X j ^ m j.succ

theorem sliceDifference_degree {n d : ℕ} (p : Polynomial (Fin (n + 1)))
    (hd : p.totalDegree ≤ d + 1) : (sliceDifference p).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  split_ifs with hzero
  · simp
  · have hmdeg := MvPolynomial.le_totalDegree hm
    have hsum : m.sum (fun _ e => e) = m 0 + ∑ j : Fin n, m j.succ := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]
    rw [hsum] at hmdeg
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_finset_prod _ _).trans
    simp only [MvPolynomial.totalDegree_X_pow]
    omega

theorem eval_monomial_cons {n : ℕ} (m : Fin (n + 1) →₀ ℕ) (c b : F₂)
    (x : Fin n → F₂) :
    MvPolynomial.eval (Fin.cons b x) (MvPolynomial.monomial m c) =
      c * b ^ m 0 * ∏ j : Fin n, x j ^ m j.succ := by
  rw [MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  simp [mul_assoc]

theorem eval_sliceDifference {n : ℕ} (p : Polynomial (Fin (n + 1)))
    (x : Fin n → F₂) :
    MvPolynomial.eval x (sliceDifference p) =
      MvPolynomial.eval (Fin.cons 0 x) p + MvPolynomial.eval (Fin.cons 1 x) p := by
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, ← Finset.sum_add_distrib]
  rw [sliceDifference, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial_cons, eval_monomial_cons]
  by_cases hm : m 0 = 0
  · simp only [hm, ↓reduceIte, map_zero, pow_zero, mul_one, one_pow]
    rw [← mul_two, show (2 : F₂) = 0 by decide, mul_zero]
  · simp [hm, zero_pow hm]

/-- Fraction of inputs on which the polynomial evaluates to one. -/
def weight {n : ℕ} (p : Polynomial (Fin n)) : ℝ := 𝔼 x : Fin n → F₂, accepted p x

theorem weight_nonneg {n : ℕ} (p : Polynomial (Fin n)) : 0 ≤ weight p := by
  apply Finset.expect_nonneg
  intro x _
  simp only [accepted]
  split_ifs <;> norm_num

theorem accepted_eq_zero_iff {σ : Type*} (p : Polynomial σ) (x : σ → F₂) :
    accepted p x = 0 ↔ MvPolynomial.eval x p = 0 := by
  obtain ⟨b, hb⟩ := boolEquivF₂.surjective (MvPolynomial.eval x p)
  cases b <;> simp [accepted, ← hb, boolEquivF₂]

theorem weight_eq_zero_iff {n : ℕ} (p : Polynomial (Fin n)) :
    weight p = 0 ↔ ∀ x, MvPolynomial.eval x p = 0 := by
  rw [weight, Finset.expect_eq_zero_iff_of_nonneg Finset.univ_nonempty]
  · simp only [Finset.mem_univ, forall_const, accepted_eq_zero_iff]
  · intro x _
    simp only [accepted]
    split_ifs <;> norm_num

theorem mean_F₂ (f : F₂ → ℝ) : (𝔼 b : F₂, f b) = (f 0 + f 1) / 2 := by
  calc
    _ = 𝔼 b : Bool, f (boolEquivF₂ b) :=
      (Fintype.expect_equiv boolEquivF₂ _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card]
      simp [Fintype.sum_bool, boolEquivF₂, add_comm]

theorem weight_slice {n : ℕ} (p : Polynomial (Fin (n + 1))) :
    weight p = (weight (slice p 0) + weight (slice p 1)) / 2 := by
  have he := Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => F₂))
    (fun z : F₂ × (Fin n → F₂) => accepted p (Fin.cons z.1 z.2)) (accepted p)
    (fun _ => rfl)
  unfold weight
  rw [← he, ← Finset.univ_product_univ, Finset.expect_product, mean_F₂]
  simp only [accepted, eval_slice]

theorem weight_difference_of_left_zero {n : ℕ} (p : Polynomial (Fin (n + 1)))
    (hz : weight (slice p 0) = 0) : weight (sliceDifference p) = weight (slice p 1) := by
  apply Finset.expect_congr rfl
  intro x _
  have hx := (weight_eq_zero_iff _).mp hz x
  rw [eval_slice] at hx
  simp only [accepted, eval_sliceDifference, hx, zero_add, eval_slice]

theorem weight_difference_of_right_zero {n : ℕ} (p : Polynomial (Fin (n + 1)))
    (hz : weight (slice p 1) = 0) : weight (sliceDifference p) = weight (slice p 0) := by
  apply Finset.expect_congr rfl
  intro x _
  have hx := (weight_eq_zero_iff _).mp hz x
  rw [eval_slice] at hx
  simp only [accepted, eval_sliceDifference, hx, add_zero, eval_slice]

theorem weight_constant {n : ℕ} (c : F₂) :
    weight (MvPolynomial.C c : Polynomial (Fin n)) = if c = 1 then 1 else 0 := by
  simp [weight, accepted]

/-- Reed--Muller minimum nonzero weight, stated for the evaluated Boolean
function. This proof does not assume that its formal polynomial is multilinear. -/
theorem minimum_weight {n d : ℕ} (p : Polynomial (Fin n)) (hd : p.totalDegree ≤ d) :
    weight p = 0 ∨ 1 / (2 : ℝ) ^ d ≤ weight p := by
  induction n generalizing d with
  | zero =>
    have heq : weight p = accepted p (fun i : Fin 0 => Fin.elim0 i) := by
      simp [weight, Fintype.expect_eq_sum_div_card]
      congr 1
    rw [heq]
    by_cases ha : MvPolynomial.eval (fun i : Fin 0 => Fin.elim0 i) p = 1
    · right
      simp only [accepted, ha, ↓reduceIte]
      apply (div_le_one (by positivity)).mpr
      exact one_le_pow₀ (by norm_num)
    · left; simp [accepted, ha]
  | succ n ih =>
    cases d with
    | zero =>
      have hp := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hd)
      rw [hp, weight_constant]
      split_ifs <;> simp
    | succ d =>
      have hd0 := (slice_degree p 0).trans hd
      have hd1 := (slice_degree p 1).trans hd
      rcases ih (slice p 0) hd0 with hz0 | h0
      · rcases ih (slice p 1) hd1 with hz1 | h1
        · left; rw [weight_slice, hz0, hz1]; norm_num
        · right
          have hdiff := ih (sliceDifference p) (sliceDifference_degree p hd)
          rw [weight_difference_of_left_zero p hz0] at hdiff
          rcases hdiff with hz1 | hdiff
          · have hpos : 0 < 1 / (2 : ℝ) ^ (d + 1) := by positivity
            linarith
          · rw [weight_slice, hz0, zero_add, pow_succ]
            rw [← div_div]
            exact div_le_div_of_nonneg_right hdiff (by norm_num)
      · rcases ih (slice p 1) hd1 with hz1 | h1
        · right
          have hdiff := ih (sliceDifference p) (sliceDifference_degree p hd)
          rw [weight_difference_of_right_zero p hz1] at hdiff
          rcases hdiff with hz0 | hdiff
          · have hpos : 0 < 1 / (2 : ℝ) ^ (d + 1) := by positivity
            linarith
          · rw [weight_slice, hz1, add_zero, pow_succ]
            rw [← div_div]
            exact div_le_div_of_nonneg_right hdiff (by norm_num)
        · right
          rw [weight_slice]
          linarith

/-- The small dyadic bias used for the adjacent-degree construction has a
uniform gap of exactly its own size. This input is proved here, without KS. -/
theorem dyadic_acceptance_gap (d : ℕ) :
    UniformAcceptanceGap d (1 / (2 : ℝ) ^ (d + 1)) (1 / (2 : ℝ) ^ (d + 1)) := by
  intro n q hq
  change 1 / (2 : ℝ) ^ (d + 1) ≤ |weight q - 1 / (2 : ℝ) ^ (d + 1)|
  have hp : 0 ≤ 1 / (2 : ℝ) ^ (d + 1) := by positivity
  rcases minimum_weight q hq with hz | hw
  · simp only [hz, zero_sub, abs_neg, abs_of_nonneg hp, le_refl]
  · have htwo : 1 / (2 : ℝ) ^ d = 2 * (1 / (2 : ℝ) ^ (d + 1)) := by
      rw [pow_succ, ← div_div]
      ring
    rw [htwo] at hw
    exact (by linarith : 1 / (2 : ℝ) ^ (d + 1) ≤ weight q - 1 / (2 : ℝ) ^ (d + 1)).trans
      (le_abs_self _)

end
end SamplingLowerBounds.PolynomialModel
