import SamplingLowerBounds.MinimumWeight
import SamplingLowerBounds.VarianceAmplification

/-!
# Unconditional explicit dyadic sampling lower bound

This combines the proved Reed--Muller minimum-weight gap, affine restriction,
and variance-sensitive amplification. It has no external acceptance-gap input.
The seed length is arbitrary, including zero, and so is the output length.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.PolynomialModel

theorem dyadic_probability_pos (d : ℕ) : 0 < 1 / (2 : ℝ)^(d+1) := by
  positivity

theorem dyadic_probability_lt_one (d : ℕ) : 1 / (2 : ℝ)^(d+1) < 1 := by
  apply (div_lt_one (by positivity)).mpr
  have h : (1 : ℝ) ≤ 2^d := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  nlinarith

theorem dyadic_cube_size (d : ℕ) :
    ((2^(d+2) : ℕ) : ℝ) * (1/(2:ℝ)^(d+1)) = 2 := by
  push_cast
  rw [show d+2 = (d+1)+1 by omega, pow_succ]
  field_simp

/-- Every degree-`d` polynomial source, at arbitrary seed length, has overlap
at most `exp(-N / 2^(3d+10))` with the explicit product of Bernoulli bits of
parameter `2^(-(d+1))`. All mathematical dependencies are proved. -/
theorem dyadic_overlap {s N d : ℕ} (Q : Source s N d) :
    CubeTilt.overlap Q.boolEval (bernoulliProduct (1/(2:ℝ)^(d+1))) ≤
      Real.exp (-((N:ℝ)/(2:ℝ)^(3*d+10))) := by
  cases N with
  | zero =>
    simpa using CubeTilt.overlap_le_one Q.boolEval (bernoulliProduct (1/(2:ℝ)^(d+1)))
  | succ N =>
    have h := cubic_overlap_bound_of_cube_gap (d+2) Q.boolEval (1/(2:ℝ)^(d+1))
      (dyadic_probability_pos d) (dyadic_probability_lt_one d) (dyadic_cube_size d)
      (by
        intro z i
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          cube_source_gap (dyadic_acceptance_gap d) Q z i)
    have heq : ((N+1:ℕ):ℝ)*(1/(2:ℝ)^(d+1))^3/128 =
        ((N+1:ℕ):ℝ)/(2:ℝ)^(3*d+10) := by
      rw [mul_div_assoc, dyadic_cubic_rate]
      ring
    simp only [Fintype.card_fin, heq] at h
    convert h using 1
    congr 1
    exact Subsingleton.elim _ _

end SamplingLowerBounds.PolynomialModel
