import SamplingLowerBounds.PolynomialModel

/-!
# Published inputs, stated as propositions rather than new axioms

Source: Khodabandeh--Shinkar, arXiv:2605.00995v1,
<https://arxiv.org/html/2605.00995v1>.

Theorem 6.4 and Remark 6.5 supply `KSOneThirdInput d` for positive degrees.
Theorem A.8 supplies `PublishedAcceptanceGap d p` for each positive degree
and fixed non-dyadic `p ∈ (0,1)`. These are theorems in the cited paper;
their proofs have not been formalized in this project. No declaration below
asserts that either proposition holds. Consumers receive an explicit proof
argument, so the external dependency stays visible in their statements.
-/

namespace SamplingLowerBounds

def PublishedAcceptanceGap (d : ℕ) (p : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ PolynomialModel.UniformAcceptanceGap d p δ

abbrev KSOneThirdInput (d : ℕ) : Prop := PublishedAcceptanceGap d (1/3)

/-- The explicit quadratic gap recorded in KS, Section 6.1. The manuscript
also sketches its standard quadratic-form proof; that proof is not yet
formalized here, so the exact numerical input remains explicit. -/
def PublishedQuadraticGap : Prop :=
  PolynomialModel.UniformAcceptanceGap 2 (1/3) (1/24)

end SamplingLowerBounds
