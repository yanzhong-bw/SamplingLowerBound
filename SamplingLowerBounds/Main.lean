import SamplingLowerBounds.Statements
import SamplingLowerBounds.DyadicSampling
import SamplingLowerBounds.HierarchySampling
import SamplingLowerBounds.FlatOptimality
import SamplingLowerBounds.SamplingConsequences
import SamplingLowerBounds.GrowingDegreeAsymptotic
import SamplingLowerBounds.SourceTranslations
import SamplingLowerBounds.HierarchyCost

/-! The short theorem surface. Read `Statements` for the exact conclusion and
`ExternalInputs` for the precise published inputs not re-proved here. -/

namespace SamplingLowerBounds.Main

theorem oneThird (d : ℕ) (hKS : KSOneThirdInput d) :
    Statements.ExponentialSeparation d (1/3) :=
  polynomial_oneThird_exponential d hKS

theorem productBias (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hgap : PublishedAcceptanceGap d p) :
    Statements.ExponentialSeparation d p := by
  obtain ⟨δ, hδ, hg⟩ := hgap
  exact polynomial_product_exponential d p δ hp hp1 hδ hg

theorem dyadicProduct {s N d : ℕ} (Q : PolynomialModel.Source s N d) :
    CubeTilt.overlap Q.boolEval (bernoulliProduct (1/(2:ℝ)^(d+1))) ≤
      Real.exp (-((N:ℝ)/(2:ℝ)^(3*d+10))) :=
  PolynomialModel.dyadic_overlap Q

theorem quadratic {s N : ℕ} (Q : PolynomialModel.Source s N 2)
    (hgap : PublishedQuadraticGap) :
    CubeTilt.overlap Q.boolEval (bernoulliProduct (1/3)) ≤
      Real.exp (-((1/(2:ℝ)^26) * (N:ℝ))) :=
  polynomial_quadratic_overlap Q hgap

/-- An actual adjacent-degree polynomial sampler, flat at exactly the
prescribed entropy, together with the seed-unrestricted overlap bound.
This theorem has no external literature hypotheses. -/
theorem hierarchy (d N k : ℕ) (hk : k ≤ N)
    (hq : 0 < FlatGraph.hierarchyBlocks d N k) :
    ∃ F : PolynomialModel.Source k N (d+1),
      (∃ j, (F.coordinate j).totalDegree = d+1) ∧
      (∀ y, CubeTilt.outputLaw F.boolEval y = 0 ∨
        CubeTilt.outputLaw F.boolEval y = 1/(2:ℝ)^k) ∧
      (∀ j, ∃ S : Finset (Fin k), S.card ≤ d+1 ∧
        ∀ x y : Fin k → PolynomialModel.F₂, (∀ a ∈ S, x a = y a) →
          F.boolEval x j = F.boolEval y j) ∧
      (∀ s (Q : PolynomialModel.Source s N d),
        CubeTilt.overlap Q.boolEval (CubeTilt.outputLaw F.boolEval) ≤
          Real.exp (-((FlatGraph.hierarchyBlocks d N k:ℝ)/(2:ℝ)^(3*d+10)))) := by
  refine ⟨FlatGraph.hierarchySampler d N k hk,
    FlatGraph.hierarchySampler_exact_degree_of_blocks d N k hk hq, ?_,
    FlatGraph.hierarchySampler_locality d N k hk, ?_⟩
  · intro y
    rw [FlatGraph.hierarchySampler_outputLaw]
    exact FlatGraph.hierarchyTarget_flat d N k hk y
  · intro s Q
    rw [FlatGraph.hierarchySampler_outputLaw]
    exact FlatGraph.hierarchy_overlap hk Q

theorem growingDegree (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ d : ℕ,
      (d:ℝ) ≤ (1-ε)/3 * (Real.log (N:ℝ)/Real.log 2) →
      ∀ s (Q : PolynomialModel.Source s N d),
        CubeTilt.overlap Q.boolEval
          (FlatGraph.hierarchyTarget d N (N/2) (Nat.div_le_self N 2)) ≤
            Real.exp (-((N:ℝ)^(ε-η))) := by
  filter_upwards [FlatGraph.growing_degree_rate_eventually ε η hε hη] with N hN
  intro d hd s Q
  have h := FlatGraph.hierarchy_overlap (Nat.div_le_self N 2) Q
  apply h.trans
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (hN d hd)

export PolynomialModel (flat_overlap_lower_bound)
export PolynomialModel (costedCanonicalSampler_cost_bound costedCanonicalSampler_is_polynomial)
export SamplingLowerBounds (polynomial_oneThird_affinity polynomial_quadratic_affinity
  polynomial_entropy_cost polynomial_quadratic_entropy_cost functional_rank_product_exponential)

/-- Strictness also holds at the level of polynomial functions/distributions,
not merely for the total degree of a chosen polynomial representative. -/
theorem hierarchy_not_degree_d {s N d k : ℕ} (hk : k ≤ N)
    (hq : 0 < FlatGraph.hierarchyBlocks d N k) (Q : PolynomialModel.Source s N d) :
    CubeTilt.outputLaw Q.boolEval ≠ FlatGraph.hierarchyTarget d N k hk := by
  intro heq
  have h := FlatGraph.hierarchy_overlap hk Q
  have hone : CubeTilt.overlap Q.boolEval (FlatGraph.hierarchyTarget d N k hk) = 1 := by
    rw [← heq]
    simp only [CubeTilt.overlap, min_self]
    exact CubeTilt.outputLaw_sum Q.boolEval
  rw [hone] at h
  have hpos : (0:ℝ) < (FlatGraph.hierarchyBlocks d N k:ℝ)/(2:ℝ)^(3*d+10) := by
    apply div_pos
    · exact_mod_cast hq
    · positivity
  exact (not_lt_of_ge h) (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hpos))

end SamplingLowerBounds.Main
