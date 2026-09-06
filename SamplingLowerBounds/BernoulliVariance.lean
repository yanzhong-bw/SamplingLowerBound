import SamplingLowerBounds.BernoulliTests

open scoped BigOperators

namespace SamplingLowerBounds.Information

theorem bernoulli_pair_variance (p : ℝ) :
    (∑ b : Bool × Bool, bernoulliMass p b.1 * bernoulliMass p b.2 *
      ((bitValue b.1-p)*(bitValue b.2-p))^2) = (p*(1-p))^2 := by
  simp [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliMass, bitValue]
  ring

theorem bernoulli_diagonal_centered_mean (p : ℝ) :
    (∑ b, bernoulliMass p b * ((bitValue b-p)^2-p*(1-p))) = 0 := by
  simp [Fintype.sum_bool, bernoulliMass, bitValue]
  ring

theorem bernoulli_diagonal_centered_variance (p : ℝ) :
    (∑ b, bernoulliMass p b * ((bitValue b-p)^2-p*(1-p))^2) =
      (1-2*p)^2*(p*(1-p)) := by
  simp [Fintype.sum_bool, bernoulliMass, bitValue]
  ring

theorem bernoulli_diagonal_variance_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ b, bernoulliMass p b * ((bitValue b-p)^2-p*(1-p))^2) ≤ p*(1-p) := by
  rw [bernoulli_diagonal_centered_variance]
  have hv : 0 ≤ p*(1-p) := mul_nonneg hp (by linarith)
  have hc : (1-2*p)^2 ≤ 1 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hc hv).trans_eq (one_mul _)

theorem bernoulli_pair_abs_le_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b : Bool × Bool) : |(bitValue b.1-p)*(bitValue b.2-p)| ≤ 1 := by
  have hpp : 0 ≤ p*(1-p) := mul_nonneg hp (by linarith)
  rcases b with ⟨b,c⟩
  cases b <;> cases c <;> simp only [bitValue, Bool.false_eq_true, ↓reduceIte] <;>
    rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg p, sq_nonneg (1-p)]

theorem bernoulli_diagonal_centered_abs_le_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b : Bool) : |(bitValue b-p)^2-p*(1-p)| ≤ 1 := by
  have hpp : 0 ≤ p*(1-p) := mul_nonneg hp (by linarith)
  cases b <;> simp only [bitValue, Bool.false_eq_true, ↓reduceIte] <;>
    rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg p, sq_nonneg (1-p)]

end SamplingLowerBounds.Information
