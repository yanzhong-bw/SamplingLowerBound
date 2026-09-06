import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.Omega

/-!
# The analytic endpoint of affine-cube amplification

This file proves the passage from the aggregate second-moment inequality to
the logarithmic overlap bound, and then to exponential overlap decay.  The
second-moment inequality itself is an explicit hypothesis; its probabilistic
derivation is not silently assumed to have been formalized here.
-/

namespace SamplingLowerBounds

/-- The exponential rate in the generic affine-cube amplification theorem. -/
noncomputable def amplificationRate (m K δ v : ℝ) : ℝ :=
  2 / (m ^ 2 * K) * (δ ^ 2 - v / K) ^ 2

/-- Squaring the nonnegative sides of the second-moment inequality gives the
logarithmic overlap lower bound.  Here `v` is the one-coordinate reference
variance and `L` is minus the logarithm of the overlap. -/
theorem secondMoment_implies_logBound
    {n K m L δ v : ℝ}
    (hn : 0 < n) (hK : 0 < K) (hm : 0 < m) (hL : 0 ≤ L)
    (hgap : 0 < δ ^ 2 - v / K)
    (hmoment : n * δ ^ 2 ≤ n * v / K + m * Real.sqrt (n * K * L / 2)) :
    2 * n / (m ^ 2 * K) * (δ ^ 2 - v / K) ^ 2 ≤ L := by
  have hrad : 0 ≤ n * K * L / 2 := by positivity
  have hlinear : n * (δ ^ 2 - v / K) ≤ m * Real.sqrt (n * K * L / 2) := by
    calc
      n * (δ ^ 2 - v / K) = n * δ ^ 2 - n * v / K := by ring
      _ ≤ m * Real.sqrt (n * K * L / 2) := by linarith
  have hleft : 0 ≤ n * (δ ^ 2 - v / K) := by positivity
  have hsquared := mul_self_le_mul_self hleft hlinear
  have hsquared' : (n * (δ ^ 2 - v / K)) ^ 2 ≤
      m ^ 2 * (n * K * L / 2) := by
    simpa only [← pow_two, mul_pow, Real.sq_sqrt hrad] using hsquared
  have hden : 0 < m ^ 2 * K := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  apply (mul_le_mul_left hn).mp
  nlinarith [hsquared']

/-- The logarithmic bound converts directly to an exponential bound. -/
theorem overlap_le_exp_of_logBound
    {ω a : ℝ} (hω : 0 < ω) (hbound : a ≤ -Real.log ω) :
    ω ≤ Real.exp (-a) := by
  calc
    ω = Real.exp (Real.log ω) := (Real.exp_log hω).symm
    _ ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)

/-- A convenient formulation of the entire analytic endpoint. -/
theorem secondMoment_implies_exponentialOverlap
    {n K m ω δ v : ℝ}
    (hn : 0 < n) (hK : 0 < K) (hm : 0 < m)
    (hω : 0 < ω) (hω_one : ω ≤ 1)
    (hgap : 0 < δ ^ 2 - v / K)
    (hmoment : n * δ ^ 2 ≤ n * v / K +
      m * Real.sqrt (n * K * (-Real.log ω) / 2)) :
    ω ≤ Real.exp (-(amplificationRate m K δ v * n)) := by
  have hL : 0 ≤ -Real.log ω := by
    have hlog : Real.log ω ≤ 0 := Real.log_nonpos hω.le hω_one
    linarith
  have hbound := secondMoment_implies_logBound hn hK hm hL hgap hmoment
  apply overlap_le_exp_of_logBound hω
  convert hbound using 1
  unfold amplificationRate
  ring

/-- The exact value of `δ² - p(1-p)/K` at the quadratic parameters
`δ = 1/24`, `p = 1/3`, and `K = 512`. -/
theorem oneThird_quadratic_gap :
    (1 / 24 : ℝ) ^ 2 - ((1 / 3 : ℝ) * (1 - 1 / 3)) / 512 = 1 / 768 := by
  norm_num

/-- The quadratic parameters give precisely the rate `2⁻²⁶`. -/
theorem oneThird_quadratic_rate :
    amplificationRate (2 / 3) 512 (1 / 24) ((1 / 3) * (1 - 1 / 3)) =
      1 / (2 : ℝ) ^ 26 := by
  norm_num [amplificationRate]

/-- The advertised numerical exponent, conditional only on the instantiated
second-moment inequality. -/
theorem oneThird_quadratic_overlap
    {n ω : ℝ} (hn : 0 < n) (hω : 0 < ω) (hω_one : ω ≤ 1)
    (hmoment : n * (1 / 24 : ℝ) ^ 2 ≤
      n * ((1 / 3 : ℝ) * (1 - 1 / 3)) / 512 +
      (2 / 3 : ℝ) * Real.sqrt (n * 512 * (-Real.log ω) / 2)) :
    ω ≤ Real.exp (-(n / (2 : ℝ) ^ 26)) := by
  have h := secondMoment_implies_exponentialOverlap hn
    (show (0 : ℝ) < 512 by norm_num)
    (show (0 : ℝ) < 2 / 3 by norm_num) hω hω_one
    (show (0 : ℝ) < (1 / 24 : ℝ) ^ 2 - ((1 / 3 : ℝ) * (1 - 1 / 3)) / 512 by
      norm_num) hmoment
  rw [oneThird_quadratic_rate] at h
  simpa only [one_div, inv_mul_eq_div] using h

/-- A power-of-two cube size exists in the required factor-two window. -/
theorem exists_dyadic_cube_size
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    ∃ t : ℕ, 1 ≤ t ∧ 1 ≤ (2 : ℝ) ^ t * δ ^ 2 ∧
      (2 : ℝ) ^ t * δ ^ 2 ≤ 2 := by
  have hsq : 0 < δ ^ 2 := by positivity
  have hx : 1 ≤ 1 / δ ^ 2 := by
    apply (le_div_iff₀ hsq).2
    nlinarith [mul_self_le_mul_self hδ.le hδ_one]
  obtain ⟨t, hlow, hhigh⟩ := exists_nat_pow_near hx (show (1 : ℝ) < 2 by norm_num)
  refine ⟨t + 1, by omega, ?_, ?_⟩
  · exact ((div_lt_iff₀ hsq).mp hhigh).le
  · have h := (le_div_iff₀ hsq).mp hlow
    rw [pow_succ]
    nlinarith

/-- The chosen size makes `δ² - p(1-p)/K` positive for `p = 1/3`. -/
theorem oneThird_gap_pos
    {K δ : ℝ} (hK : 0 < K) (hsize_lower : 1 ≤ K * δ ^ 2) :
    0 < δ ^ 2 - (2 / 9 : ℝ) / K := by
  have hinv_upper : 1 / K ≤ δ ^ 2 := by
    apply (div_le_iff₀ hK).2
    nlinarith
  have hδ : 0 < δ ^ 2 := lt_of_lt_of_le (by positivity : 0 < 1 / K) hinv_upper
  have hrewrite : (2 / 9 : ℝ) / K = (2 / 9 : ℝ) * (1 / K) := by ring
  rw [hrewrite]
  nlinarith

/-- For the one-third target, any cube size in the indicated multiplicative
window gives the stronger intermediate constant `49 / 36`.

The window is written without reciprocal powers: for positive `δ`, the two
bounds are equivalent to `δ⁻² ≤ K ≤ 2 δ⁻²`.  Thus the theorem applies in
particular to the next power of two used in the manuscript. -/
theorem oneThird_rate_lower_bound
    {K δ : ℝ} (hK : 0 < K)
    (hsize_lower : 1 ≤ K * δ ^ 2) (hsize_upper : K * δ ^ 2 ≤ 2) :
    (49 / 36 : ℝ) * δ ^ 6 ≤ amplificationRate (2 / 3) K δ (2 / 9) := by
  have hinv_upper : 1 / K ≤ δ ^ 2 := by
    apply (div_le_iff₀ hK).2
    nlinarith
  have hinv_lower : δ ^ 2 / 2 ≤ 1 / K := by
    apply (le_div_iff₀ hK).2
    nlinarith
  have hgap : (7 / 9 : ℝ) * δ ^ 2 ≤ δ ^ 2 - (2 / 9 : ℝ) * (1 / K) := by
    nlinarith
  have hgap_nonneg : 0 ≤ (7 / 9 : ℝ) * δ ^ 2 := by positivity
  have hsquared := mul_self_le_mul_self hgap_nonneg hgap
  have hsquared' : ((7 / 9 : ℝ) * δ ^ 2) ^ 2 ≤
      (δ ^ 2 - (2 / 9 : ℝ) * (1 / K)) ^ 2 := by
    simpa only [pow_two] using hsquared
  have hfirst := mul_le_mul_of_nonneg_right hinv_lower
    (sq_nonneg (δ ^ 2 - (2 / 9 : ℝ) * (1 / K)))
  have hsecond := mul_le_mul_of_nonneg_left hsquared'
    (show 0 ≤ δ ^ 2 / 2 by positivity)
  have hrate : amplificationRate (2 / 3) K δ (2 / 9) =
      (9 / 2 : ℝ) * ((1 / K) * (δ ^ 2 - (2 / 9 : ℝ) * (1 / K)) ^ 2) := by
    unfold amplificationRate
    field_simp [ne_of_gt hK]
    ring
  rw [hrate]
  nlinarith [hfirst, hsecond]

/-- In particular, the rate is at least `δ⁶`, where `δ` is the lower bound
on each coordinate mean's distance from `1/3`. This numerical statement does not
invoke any result about polynomial acceptance probabilities. -/
theorem oneThird_rate_ge_gap_sixth
    {K δ : ℝ} (hK : 0 < K)
    (hsize_lower : 1 ≤ K * δ ^ 2) (hsize_upper : K * δ ^ 2 ≤ 2) :
    δ ^ 6 ≤ amplificationRate (2 / 3) K δ (2 / 9) := by
  have h := oneThird_rate_lower_bound hK hsize_lower hsize_upper
  have hδ : 0 ≤ δ ^ 6 := by positivity
  nlinarith

/-- The variance-sensitive endpoint used for the small-target-probability hierarchy. The
inputs state exactly the numerical estimates required of the reference
variance and cube size; the moment inequality is explicit. -/
theorem varianceSecondMoment_implies_logBound
    {n K p v L : ℝ}
    (hn : 0 < n) (hK : 0 < K) (hp : 0 < p) (hp_one : p ≤ 1)
    (hKp : K * p = 2) (_hv : 0 ≤ v) (hvp : v ≤ p) (_hL : 0 ≤ L)
    (hmoment : n * p ^ 2 ≤ n * v / K +
      2 * (v + Real.sqrt v / K) * Real.sqrt (n * K * L) + K * L) :
    n * p ^ 3 / 128 < L := by
  by_contra! hsmall
  have hKL : K * L ≤ n * p ^ 2 / 64 := by
    calc
      K * L ≤ K * (n * p ^ 3 / 128) :=
        mul_le_mul_of_nonneg_left hsmall hK.le
      _ = (K * p) * (n * p ^ 2 / 128) := by ring
      _ = n * p ^ 2 / 64 := by rw [hKp]; ring
  have hfirst : n * v / K ≤ n * p ^ 2 / 2 := by
    apply (div_le_iff₀ hK).2
    calc
      n * v ≤ n * p := mul_le_mul_of_nonneg_left hvp hn.le
      _ = n * p * (K * p) / 2 := by rw [hKp]; ring
      _ = n * p ^ 2 / 2 * K := by ring
  have hsqrt : Real.sqrt v ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith
  have hKv : K * v ≤ K * p := mul_le_mul_of_nonneg_left hvp hK.le
  have hcoef : 2 * (v + Real.sqrt v / K) ≤ 3 * p := by
    apply (mul_le_mul_right hK).mp
    have heq : (2 * (v + Real.sqrt v / K)) * K =
        2 * (K * v + Real.sqrt v) := by
      field_simp [ne_of_gt hK]
      ring
    rw [heq]
    nlinarith
  have hroot : Real.sqrt (n * K * L) ≤ n * p / 8 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h := mul_le_mul_of_nonneg_left hKL hn.le
      nlinarith
  have hproduct := mul_le_mul hcoef hroot
    (Real.sqrt_nonneg (n * K * L)) (show 0 ≤ 3 * p by positivity)
  have hpositive : 0 < n * p ^ 2 := by positivity
  nlinarith [hfirst, hproduct, hKL]

/-- Exponential overlap decay at rate `p³ / 128` follows from the
variance-sensitive second-moment inequality. -/
theorem varianceSecondMoment_implies_exponentialOverlap
    {n K p v ω : ℝ}
    (hn : 0 < n) (hK : 0 < K) (hp : 0 < p) (hp_one : p ≤ 1)
    (hKp : K * p = 2) (hv : 0 ≤ v) (hvp : v ≤ p)
    (hω : 0 < ω) (hω_one : ω ≤ 1)
    (hmoment : n * p ^ 2 ≤ n * v / K +
      2 * (v + Real.sqrt v / K) * Real.sqrt (n * K * (-Real.log ω)) +
      K * (-Real.log ω)) :
    ω ≤ Real.exp (-(n * p ^ 3 / 128)) := by
  have hL : 0 ≤ -Real.log ω := by
    have hlog := Real.log_nonpos hω.le hω_one
    linarith
  have hbound := varianceSecondMoment_implies_logBound hn hK hp hp_one
    hKp hv hvp hL hmoment
  exact overlap_le_exp_of_logBound hω hbound.le

/-- The dyadic specialization matches the hierarchy exponent in the paper. -/
theorem dyadic_cubic_rate (d : ℕ) :
    ((1 / (2 : ℝ) ^ (d + 1)) ^ 3) / 128 =
      1 / (2 : ℝ) ^ (3 * d + 10) := by
  rw [div_pow, one_pow, div_div, ← pow_mul]
  congr 1
  rw [show 3 * d + 10 = (d + 1) * 3 + 7 by omega, pow_add]
  norm_num

end SamplingLowerBounds
