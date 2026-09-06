import SamplingLowerBounds.FlatOptimality
import SamplingLowerBounds.ActualAmplification
import SamplingLowerBounds.EntropyDecomposition

/-!
# The explicit one-third lower witness and exact flat entropy

The first theorem computes the overlap of a concrete constant polynomial
sampler. The entropy identity uses natural logarithms, so k bits equal k log 2.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds
open PolynomialModel Information CubeTilt FlatGraph

/-- The all-zero source proves the lower bound in the introduction for
every output length and every permitted polynomial degree. -/
theorem oneThird_constant_overlap (N d : ℕ) :
    overlap (constantSource N d (fun _ => false)).boolEval (bernoulliProduct (1/3)) =
      (2/3:ℝ)^N := by
  have hzero : bernoulliProduct (1/3) (fun _ : Fin N => false) = (2/3:ℝ)^N := by
    norm_num [bernoulliProduct, productMass, bernoulliMass, div_pow]
  change massOverlap (outputLaw (constantSource N d (fun _ => false)).boolEval)
    (bernoulliProduct (1/3)) = _
  rw [constantSource_outputLaw, pointMass_overlap]
  · exact hzero
  · intro b
    exact (bernoulliProduct_pos (1/3) (by norm_num) (by norm_num) b).le
  · rw [hzero]
    exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Normalized flat masses 0 or 2^(-k) have Shannon entropy exactly k bits. -/
theorem finiteEntropy_flat {A : Type*} [Fintype A]
    (P : A → ℝ) (k : ℕ) (hsum : ∑ x, P x = 1)
    (hflat : ∀ x, P x = 0 ∨ P x = 1/(2:ℝ)^k) :
    finiteEntropy P = (k:ℝ)*Real.log 2 := by
  have hpoint (x : A) : P x * Real.log (P x) = P x * (-((k:ℝ)*Real.log 2)) := by
    rcases hflat x with hx | hx
    · simp [hx]
    · rw [hx]
      congr 1
      simp [one_div, Real.log_inv, Real.log_pow]
  unfold finiteEntropy
  simp_rw [hpoint]
  rw [← Finset.sum_mul, hsum, one_mul, neg_neg]

end SamplingLowerBounds
