import SamplingLowerBounds.SecondMoment
import SamplingLowerBounds.FiniteInformation
import SamplingLowerBounds.Endpoint

/-!
# Assembly of the finite second-moment argument

These are conditional assembly theorems. The probability law may be any
finite law, including a tilted affine-cube law. Pointwise lower bounds on each
coordinate mean's distance from the target probability and coordinate information
bounds are explicit hypotheses. Pinsker and KL tensorization are proved in
the information modules; `ActualAmplification` derives the hypotheses below
for the actual overlap-induced cube law.
The external result about polynomial acceptance probabilities
(Khodabandeh--Shinkar [KS26, Theorem 6.4 and Remark 6.5] for target `1/3`, and
[KS26, Theorem A.8] for fixed non-dyadic targets) is also not formalized here.
-/

open scoped BigOperators

namespace SamplingLowerBounds

variable {Ω V I : Type*} [Fintype Ω] [Fintype V] [Fintype I]
  [Nonempty V] [Nonempty I]

/-- Exponential separation from pointwise lower bounds on each coordinate
mean's distance from the target probability and bounds on the one- and two-vertex
moments. -/
theorem amplification_of_moment_bounds
    (μ : Ω → ℝ) (hμnonneg : ∀ x, 0 ≤ μ x) (hμsum : ∑ x, μ x = 1)
    (Y : Ω → V → I → ℝ) (p δ variance m ω : ℝ)
    (hδ : 0 ≤ δ) (hm : 0 < m) (hω : 0 < ω) (hω_one : ω ≤ 1)
    (hvariance : 0 < δ ^ 2 - variance / (Fintype.card V : ℝ))
    (hgap : ∀ x i,
      δ ≤ |(∑ v, Y x v i) / (Fintype.card V : ℝ) - p|)
    (hdiag : ∀ v, SecondMoment.moment μ Y p v v ≤
      (Fintype.card I : ℝ) * variance +
        m * Real.sqrt ((Fintype.card I : ℝ) * (Fintype.card V : ℝ) *
          (-Real.log ω) / 2))
    (hoff : ∀ v w, v ≠ w → SecondMoment.moment μ Y p v w ≤
      m * Real.sqrt ((Fintype.card I : ℝ) * (Fintype.card V : ℝ) *
        (-Real.log ω) / 2)) :
    ω ≤ Real.exp (-(amplificationRate m (Fintype.card V : ℝ) δ variance *
      (Fintype.card I : ℝ))) := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hK : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply secondMoment_implies_exponentialOverlap hn hK hm hω hω_one hvariance
  exact SecondMoment.bias_gap_second_moment_bound μ hμnonneg hμsum
    Y p δ variance _ hδ hgap hdiag hoff

/-- Assembly one step earlier, from per-coordinate error estimates and
their information budget. The hypotheses `hlocal` and `hbudget` are the
numerical conclusions of Pinsker and KL tensorization; they are not axioms. -/
theorem amplification_of_coordinate_information [DecidableEq V]
    (μ : Ω → ℝ) (hμnonneg : ∀ x, 0 ≤ μ x) (hμsum : ∑ x, μ x = 1)
    (Y : Ω → V → I → ℝ) (p δ variance m ω : ℝ)
    (hδ : 0 ≤ δ) (hm : 0 < m) (hω : 0 < ω) (hω_one : ω ≤ 1)
    (hvariance : 0 < δ ^ 2 - variance / (Fintype.card V : ℝ))
    (hgap : ∀ x i,
      δ ≤ |(∑ v, Y x v i) / (Fintype.card V : ℝ) - p|)
    (d : V → V → I → ℝ) (hd : ∀ v w i, 0 ≤ d v w i)
    (hbudget : ∀ v w, ∑ i, d v w i ≤ (Fintype.card V : ℝ) * (-Real.log ω))
    (hlocal : ∀ v w i,
      |SecondMoment.expectation μ (fun x => (Y x v i - p) * (Y x w i - p)) -
        (if v = w then variance else 0)| ≤ m * Real.sqrt (d v w i / 2)) :
    ω ≤ Real.exp (-(amplificationRate m (Fintype.card V : ℝ) δ variance *
      (Fintype.card I : ℝ))) := by
  classical
  have htests (v w : V) := Information.coordinate_test_sum_bound
    (fun i => SecondMoment.expectation μ
      (fun x => (Y x v i - p) * (Y x w i - p)) -
        (if v = w then variance else 0))
    (d v w) m ((Fintype.card V : ℝ) * (-Real.log ω)) hm.le
    (hd v w) (hbudget v w) (hlocal v w)
  apply amplification_of_moment_bounds μ hμnonneg hμsum Y p δ variance m ω
    hδ hm hω hω_one hvariance hgap
  · intro v
    have h := (le_abs_self _).trans (htests v v)
    simp only [ite_true, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at h
    dsimp [SecondMoment.moment]
    convert (sub_le_iff_le_add.mp h) using 1
    ring_nf
  · intro v w hvw
    have h := (le_abs_self _).trans (htests v w)
    simpa only [hvw, ite_false, sub_zero, ← mul_assoc,
      SecondMoment.moment] using h

end SamplingLowerBounds
