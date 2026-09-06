import SamplingLowerBounds.GrowingDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform asymptotics for the logarithmic degree range

For every fixed exponent loss η>0, a single threshold works simultaneously
for every degree in the manuscript's logarithmic range. This states the
`N^(ε-o(1))` exponent with explicit quantifiers rather than informal notation.
-/

open Filter Asymptotics
open scoped Topology

namespace SamplingLowerBounds.FlatGraph

theorem eventually_log_degree_loss_le_rpow (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      C * (Real.log (N:ℝ) / Real.log 2 + 1) ≤ (N:ℝ)^η := by
  have hlog := isLittleO_log_rpow_atTop hη
  have hone : (fun _ : ℝ => (1:ℝ)) =o[atTop] (fun x : ℝ => x^η) :=
    (Real.isLittleO_const_log_atTop (c := 1)).trans hlog
  have hdiv : (fun x : ℝ => Real.log x / Real.log 2) =o[atTop]
      (fun x : ℝ => x^η) := by
    simpa only [div_eq_mul_inv, mul_comm] using hlog.const_mul_left (Real.log 2)⁻¹
  have hall := (hdiv.add hone).const_mul_left C
  have hevent := (hall.bound (by norm_num : (0:ℝ) < 1))
  have hnat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually hevent
  filter_upwards [hnat] with N hN
  have hn : 0 ≤ (N:ℝ)^η := Real.rpow_nonneg (Nat.cast_nonneg N) η
  have habs : |C * (Real.log (N:ℝ) / Real.log 2 + 1)| ≤ (N:ℝ)^η := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn, one_mul] using hN
  exact (le_abs_self _).trans habs

/-- The size threshold and subpolynomial denominator loss hold uniformly
over every degree in the prescribed logarithmic range. -/
theorem growing_degree_eventual_parameters (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      (d:ℝ) ≤ (1-ε)/3 * (Real.log (N:ℝ)/Real.log 2) →
        8*(d+1) ≤ N ∧ (2:ℝ)^12*((d:ℝ)+1) ≤ (N:ℝ)^η := by
  filter_upwards [eventually_log_degree_loss_le_rpow 8 1 (by norm_num),
    eventually_log_degree_loss_le_rpow ((2:ℝ)^12) η hη,
    eventually_ge_atTop (1:ℕ)] with N hsize hloss hN
  intro d hd
  have hlog : 0 ≤ Real.log (N:ℝ)/Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hN))
      (Real.log_nonneg (by norm_num))
  have hdlog : (d:ℝ) ≤ Real.log (N:ℝ)/Real.log 2 :=
    hd.trans (mul_le_of_le_one_left hlog (by linarith : (1-ε)/3 ≤ 1))
  constructor
  · have hs : (8:ℝ)*((d:ℝ)+1) ≤ N := by
      simp only [Real.rpow_one] at hsize
      linarith
    exact_mod_cast hs
  · exact (mul_le_mul_of_nonneg_left (add_le_add_right hdlog 1) (by positivity)).trans hloss

/-- Precise meaning of the rate `N^(ε-o(1))`: for each fixed loss η>0,
one threshold works for all degrees satisfying the logarithmic constraint. -/
theorem growing_degree_rate_eventually (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      (d:ℝ) ≤ (1-ε)/3 * (Real.log (N:ℝ)/Real.log 2) →
        (N:ℝ)^(ε-η) ≤ (hierarchyBlocks d N (N/2):ℝ)/(2:ℝ)^(3*d+10) := by
  filter_upwards [growing_degree_eventual_parameters ε η hε hη,
    eventually_ge_atTop (1:ℕ)] with N hparam hN
  intro d hd
  obtain ⟨hsize, hloss⟩ := hparam d hd
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hden : 0 < (2:ℝ)^12*((d:ℝ)+1) := by positivity
  calc
    (N:ℝ)^(ε-η) = (N:ℝ)^ε/(N:ℝ)^η := Real.rpow_sub hNp ε η
    _ ≤ (N:ℝ)^ε/((2:ℝ)^12*((d:ℝ)+1)) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hNp.le _) hden hloss
    _ ≤ _ := growing_degree_rate N d ε hsize hd

end SamplingLowerBounds.FlatGraph
