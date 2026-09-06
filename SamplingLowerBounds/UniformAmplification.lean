import SamplingLowerBounds.ActualAmplification

open scoped BigOperators
open Classical

namespace SamplingLowerBounds

/-- The cube dimension is chosen internally. The rate `δ^6` is independent
of the seed group, its cardinality, and the number of output coordinates. -/
theorem oneThird_overlap_of_uniform_cube_gap
    {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [Nonempty I]
    (Q : G → I → Bool) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : ∀ (t : ℕ) (z : CubeTilt.Parameters G t) (i : I),
      δ ≤ |(∑ v : Cube.Tuple Bool t,
        Information.bitValue (CubeTilt.vertexOutput t Q v z i)) /
        ((2 ^ t : ℕ) : ℝ) - (1/3 : ℝ)|) :
    CubeTilt.overlap Q (bernoulliProduct (1/3)) ≤
      Real.exp (-(δ^6 * (Fintype.card I : ℝ))) := by
  obtain ⟨t, _, hlo, hhi⟩ := exists_dyadic_cube_size hδ hδ1
  have hK : 0 < (2 : ℝ)^t := by positivity
  have hvar := oneThird_gap_pos hK hlo
  have hb := overlap_bound_of_cube_gap t Q (1/3) δ
    (by norm_num) (by norm_num) hδ.le
    (by norm_num only [Nat.cast_pow, Nat.cast_ofNat] at *; convert hvar using 1)
    (hgap t)
  have hr := oneThird_rate_ge_gap_sixth hK hlo hhi
  have hv : (1/3 : ℝ)*(1-1/3) = 2/9 := by norm_num
  have hm : max (1/3 : ℝ) (1-1/3) = 2/3 := by norm_num
  rw [hm, hv] at hb
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hb
  exact hb.trans (Real.exp_le_exp.mpr (neg_le_neg
    (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _))))

end SamplingLowerBounds
