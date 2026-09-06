import SamplingLowerBounds.FinitePinsker

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.Information

/-- Aggregate bounded coordinate tests against an actual product reference law.
Neither a coordinate Pinsker bound nor tensorization is assumed. -/
theorem product_coordinate_test {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (M : I → A → ℝ)
    (hR : ∀ x, 0 ≤ R x) (hRsum : ∑ x, R x = 1)
    (hM : ∀ i x, 0 < M i x) (hMsum : ∀ i, ∑ x, M i x = 1)
    (g : I → A → ℝ) (a : ℝ) (c : I → ℝ) (ha : 0 ≤ a)
    (hg : ∀ i x, |g i x - c i| ≤ a / 2) :
    |∑ i, ((∑ x, R x * g i (x i)) - ∑ b, M i b * g i b)| ≤
      a * Real.sqrt ((Fintype.card I : ℝ) * finiteKL R (productMass M) / 2) := by
  apply coordinate_test_sum_bound _ (fun i => finiteKL (marginal R i) (M i))
    a (finiteKL R (productMass M)) ha
  · intro i
    exact finiteKL_nonneg _ _ (marginal_nonneg R hR i)
      (marginal_sum R hRsum i) (hMsum i) (hM i)
  · exact finiteKL_tensorization R M hR hRsum hM
  · intro i
    have h := finite_coordinate_test (marginal R i) (M i)
      (marginal_nonneg R hR i) (hM i) (marginal_sum R hRsum i)
      (hMsum i) (g i) a (c i) ha (hg i)
    rwa [marginal_expectation] at h

end SamplingLowerBounds.Information
