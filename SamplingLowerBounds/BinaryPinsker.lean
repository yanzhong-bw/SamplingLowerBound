import SamplingLowerBounds.FiniteInformation
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith

open Set

namespace SamplingLowerBounds.Information

noncomputable def binaryKL (q p : ℝ) : ℝ :=
  q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))

theorem mul_log_div (q p : ℝ) (hp : p ≠ 0) :
    q * Real.log (q / p) = q * Real.log q - q * Real.log p := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [Real.log_div hq hp]; ring

theorem binaryKL_eq_entropy (q p : ℝ) (hp : p ≠ 0) (hp1 : p ≠ 1) :
    binaryKL q p = -Real.binEntropy q - q * Real.log p -
      (1 - q) * Real.log (1 - p) := by
  rw [binaryKL, mul_log_div q p hp, mul_log_div (1-q) (1-p) (sub_ne_zero.mpr hp1.symm)]
  simp only [Real.binEntropy, Real.log_inv]
  ring

theorem binary_pinsker (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1) : 2 * (q - p)^2 ≤ binaryKL q p := by
  let f : ℝ → ℝ := fun x => -Real.binEntropy x - x * Real.log p -
    (1-x) * Real.log (1-p) - 2 * (x-p)^2
  let f' : ℝ → ℝ := fun x => -(Real.log (1-x) - Real.log x) - Real.log p +
    Real.log (1-p) - 4*(x-p)
  let f'' : ℝ → ℝ := fun x => 1/(1-x) + 1/x - 4
  have hd (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : HasDerivAt f (f' x) x := by
    have hb := Real.hasDerivAt_binEntropy hx.1.ne' (ne_of_lt hx.2)
    have hlin := (hasDerivAt_id x).mul_const (Real.log p)
    have hlin' := ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).mul_const
      (Real.log (1-p))
    have hquad := (((hasDerivAt_id x).sub_const p).pow 2).const_mul 2
    convert ((hb.neg.sub hlin).sub hlin').sub hquad using 1; dsimp [f, f']; ring
  have hdd (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : HasDerivAt f' (f'' x) x := by
    have hx1 : 1-x ≠ 0 := (sub_pos.mpr hx.2).ne'
    have hlog := ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).log hx1
    have hlog' := Real.hasDerivAt_log hx.1.ne'
    have hlin := ((hasDerivAt_id x).sub_const p).const_mul 4
    convert (((hlog.sub hlog').neg.sub_const (Real.log p)).add_const
      (Real.log (1-p))).sub hlin using 1; dsimp [f', f'']; ring
  have hnonneg (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : 0 ≤ f'' x := by
    have hx1 : 0 < 1-x := sub_pos.mpr hx.2
    have heq : f'' x = (1-4*x*(1-x))/(x*(1-x)) := by
      dsimp [f'']; field_simp [hx.1.ne', hx1.ne']; ring
    rw [heq]
    apply div_nonneg _ (mul_pos hx.1 hx1).le
    nlinarith [sq_nonneg (2*x-1)]
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (f' := f') (f'' := f'')
    · dsimp [f]; fun_prop
    · intro x hx
      exact (hd x (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      exact (hdd x (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      exact hnonneg x (by simpa using hx)
  have hpderiv : HasDerivAt f 0 p := by
    simpa [f'] using hd p ⟨hp0,hp1⟩
  have hpval : f p = 0 := by
    dsimp [f]
    simp only [Real.binEntropy, Real.log_inv]
    ring
  have hmin : f p ≤ f q := by
    rcases lt_trichotomy p q with hpq | heq | hqp
    · have hs := hconv.le_slope_of_hasDerivAt ⟨hp0.le,hp1.le⟩ ⟨hq0,hq1⟩ hpq hpderiv
      rw [slope_def_field] at hs
      have := (le_div_iff₀ (sub_pos.mpr hpq)).mp hs
      linarith
    · simp [heq]
    · have hs := hconv.slope_le_of_hasDerivAt ⟨hq0,hq1⟩ ⟨hp0.le,hp1.le⟩ hqp hpderiv
      rw [slope_def_field] at hs
      have := (div_le_iff₀ (sub_pos.mpr hqp)).mp hs
      linarith
  rw [hpval] at hmin
  rw [binaryKL_eq_entropy q p hp0.ne' (ne_of_lt hp1)]
  dsimp [f] at hmin
  linarith

end SamplingLowerBounds.Information
