import SamplingLowerBounds.PolynomialSampling

namespace SamplingLowerBounds.Statements

/-- The same rate works for every seed length and every output length.
`Source` contains actual polynomials and their total-degree bounds. -/
def ExponentialSeparation (d : ℕ) (p : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (s N : ℕ) (Q : PolynomialModel.Source s N d),
    CubeTilt.overlap Q.boolEval (bernoulliProduct p) ≤
      Real.exp (-(c * (N : ℝ)))

end SamplingLowerBounds.Statements
