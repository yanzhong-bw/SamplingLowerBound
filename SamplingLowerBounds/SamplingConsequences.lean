import SamplingLowerBounds.PolynomialHellinger
import SamplingLowerBounds.EntropyDecomposition
import SamplingLowerBounds.FunctionalRank

open scoped BigOperators
open Classical

namespace SamplingLowerBounds
open PolynomialModel Information

/-- The functional-rank extension uses the explicitly constructed polynomial
representative; `eval_toPolynomialSource` proves equality of its output map. -/
theorem functional_rank_product_exponential (d r : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hgap : PublishedAcceptanceGap (d*r) p) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s N : ℕ) (Q : FunctionalSource s N d r),
      CubeTilt.overlap Q.toPolynomialSource.boolEval (bernoulliProduct p) ≤
        Real.exp (-(c * (N : ℝ))) := by
  obtain ⟨δ, hδ, hg⟩ := hgap
  obtain ⟨c, hc, h⟩ := polynomial_product_exponential (d*r) p δ hp hp1 hδ hg
  exact ⟨c, hc, fun s N Q => h s N Q.toPolynomialSource⟩

/-- The complete entropy-cost corollary for actual polynomial maps and
arbitrary normalized input laws, relative only to the uniform KS gap. -/
theorem polynomial_entropy_cost {s N d : ℕ} (Q : Source s N d)
    (δ : ℝ) (hδ : 0 < δ) (hgap : UniformAcceptanceGap d (1/3) δ)
    (nu : (Fin s → F₂) → ℝ) (hnu : ∀ x, 0 ≤ nu x) (hsum : ∑ x, nu x = 1) :
    δ^6 * (N:ℝ) ≤ (s:ℝ)*Real.log 2 - finiteEntropy nu +
      totalCorrelation (pushMass nu Q.boolEval) +
        ∑ i, binaryKL (marginal (pushMass nu Q.boolEval) i true) (1/3) := by
  have hbc : bhattacharyyaCoeff (pushMass (CubeTilt.uniformMass (Fin s → F₂)) Q.boolEval)
      (productMass (fun _ : Fin N => bernoulliMass (1/3))) ≤
        Real.exp (-(δ^6 * (N:ℝ))/2) := by
    convert polynomial_oneThird_affinity Q δ hδ hgap using 1
  have h := sampler_entropy_cost_ge_of_affinity_bound nu Q.boolEval hnu hsum
    (1/3) (δ^6 * (N:ℝ)) (by norm_num) (by norm_num)
    (by convert hbc using 1; congr 1; exact Subsingleton.elim _ _)
  have hcard : Real.log (Fintype.card (Fin s → F₂) : ℝ) = (s:ℝ)*Real.log 2 := by
    simp [Fintype.card_fun, F₂, Real.log_pow]
  rw [hcard] at h
  exact h

theorem polynomial_quadratic_entropy_cost {s N : ℕ} (Q : Source s N 2)
    (hgap : PublishedQuadraticGap)
    (nu : (Fin s → F₂) → ℝ) (hnu : ∀ x, 0 ≤ nu x) (hsum : ∑ x, nu x = 1) :
    (1/(2:ℝ)^26) * (N:ℝ) ≤ (s:ℝ)*Real.log 2 - finiteEntropy nu +
      totalCorrelation (pushMass nu Q.boolEval) +
        ∑ i, binaryKL (marginal (pushMass nu Q.boolEval) i true) (1/3) := by
  have hbc := polynomial_quadratic_affinity Q hgap
  have h := sampler_entropy_cost_ge_of_affinity_bound nu Q.boolEval hnu hsum
    (1/3) ((1/(2:ℝ)^26) * (N:ℝ)) (by norm_num) (by norm_num)
    (by convert hbc using 1; congr 1; exact Subsingleton.elim _ _)
  have hcard : Real.log (Fintype.card (Fin s → F₂) : ℝ) = (s:ℝ)*Real.log 2 := by
    simp [Fintype.card_fun, F₂, Real.log_pow]
  rw [hcard] at h
  exact h

end SamplingLowerBounds
