import SamplingLowerBounds.AndBlocks
import SamplingLowerBounds.DyadicSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A finite bound for growing degrees at half entropy

The final exponent comparison is proved under explicit size and logarithmic
degree constraints. There is no unquantified sufficiently-large-N assumption.
-/

open scoped BigOperators

namespace SamplingLowerBounds.FlatGraph

theorem hierarchyBlocks_half (d N : ℕ) :
    hierarchyBlocks d N (N/2) = N/(2*(d+1)) := by
  unfold hierarchyBlocks
  have h : N/2/(d+1) ≤ N-N/2 := by
    have hh := Nat.div_le_self (N/2) (d+1)
    omega
  rw [min_eq_left h, Nat.div_div_eq_div_mul]

/-- Explicit half-entropy block lower bound. -/
theorem hierarchyBlocks_half_lower (d N : ℕ) (hN : 8*(d+1) ≤ N) :
    (N:ℝ)/(4*((d:ℝ)+1)) ≤ (hierarchyBlocks d N (N/2):ℝ) := by
  have hnat : N ≤ 4*(d+1)*hierarchyBlocks d N (N/2) := by
    rw [hierarchyBlocks_half]
    have hm : 0 < 2*(d+1) := by omega
    have hdiv : 1 ≤ N/(2*(d+1)) := (Nat.one_le_div_iff hm).mpr (by omega)
    have hlt := Nat.lt_mul_div_succ N hm
    have hmul := Nat.mul_le_mul_left (2*(d+1)) hdiv
    nlinarith
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 4*((d:ℝ)+1))).mpr
  exact_mod_cast (by nlinarith [hnat] : N ≤ hierarchyBlocks d N (N/2)*(4*(d+1)))

/-- The logarithmic degree constraint bounds the power-of-two rate loss. -/
theorem growing_degree_power_bound (N d : ℕ) (ε : ℝ) (hN : 0 < N)
    (hd : (d:ℝ) ≤ (1-ε)/3 * (Real.log (N:ℝ)/Real.log 2)) :
    (N:ℝ)^ε * (2:ℝ)^(3*d) ≤ N := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.log 2 * ((3*d:ℕ):ℝ) ≤ Real.log (N:ℝ)*(1-ε) := by
    have h := mul_le_mul_of_nonneg_right hd hlog2.le
    have he : ((1-ε)/3 * (Real.log (N:ℝ)/Real.log 2))*Real.log 2 =
        (1-ε)/3*Real.log (N:ℝ) := by field_simp; ring
    rw [he] at h
    push_cast
    nlinarith
  have hpow : (2:ℝ)^(3*d) ≤ (N:ℝ)^(1-ε) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
      Real.rpow_def_of_pos hNp]
    exact Real.exp_le_exp.mpr hexp
  calc
    (N:ℝ)^ε * (2:ℝ)^(3*d) ≤ (N:ℝ)^ε * (N:ℝ)^(1-ε) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hNp.le _)
    _ = N := by rw [← Real.rpow_add hNp]; simp

/-- The exact finite exponent in the growing-degree corollary. -/
theorem growing_degree_rate (N d : ℕ) (ε : ℝ) (hN : 8*(d+1) ≤ N)
    (hd : (d:ℝ) ≤ (1-ε)/3 * (Real.log (N:ℝ)/Real.log 2)) :
    (N:ℝ)^ε / ((2:ℝ)^12*((d:ℝ)+1)) ≤
      (hierarchyBlocks d N (N/2):ℝ)/(2:ℝ)^(3*d+10) := by
  have hNpos : 0 < N := by omega
  have hpower := growing_degree_power_bound N d ε hNpos hd
  have hblocks := hierarchyBlocks_half_lower d N hN
  have hq : (N:ℝ) ≤ 4*((d:ℝ)+1)*(hierarchyBlocks d N (N/2):ℝ) := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ)<4*((d:ℝ)+1))).mp hblocks
    nlinarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    (N:ℝ)^ε * (2:ℝ)^(3*d+10) = 1024*((N:ℝ)^ε*(2:ℝ)^(3*d)) := by
      rw [pow_add]
      norm_num
      ring
    _ ≤ 1024*(4*((d:ℝ)+1)*(hierarchyBlocks d N (N/2):ℝ)) := by
      nlinarith [hpower.trans hq]
    _ = _ := by norm_num; ring

end SamplingLowerBounds.FlatGraph
