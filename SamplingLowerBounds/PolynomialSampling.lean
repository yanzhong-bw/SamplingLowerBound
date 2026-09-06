import SamplingLowerBounds.UniformAmplification
import SamplingLowerBounds.PolynomialModel
import SamplingLowerBounds.ExternalInputs

/-!
# Polynomial sampling lower bounds relative to a precisely stated external input

`KSOneThirdInput` records the conclusion of Khodabandeh--Shinkar,
arXiv:2605.00995v1, Theorem 6.4 and Remark 6.5. It is a proposition,
not a declared axiom. Each result taking this input states that dependency.
The affine restriction, choice of cube dimension, and complete amplification
from the actual output distribution are all proved in this development.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds
open PolynomialModel

/-- A genuine output distribution of an actual polynomial sampler, with no
remaining moment or information-budget assumptions. -/
theorem polynomial_oneThird_overlap {s N d : ℕ} (Q : Source s N d)
    (δ : ℝ) (hδ : 0 < δ) (hgap : UniformAcceptanceGap d (1/3) δ) :
    CubeTilt.overlap Q.boolEval (bernoulliProduct (1/3)) ≤
      Real.exp (-(δ^6 * (N : ℝ))) := by
  by_cases hN : N = 0
  · subst N
    simpa using CubeTilt.overlap_le_one Q.boolEval (bernoulliProduct (1/3))
  · letI : NeZero N := ⟨hN⟩
    have hδ1 : δ ≤ 1 := by
      have hzero := hgap 0 0 (by simp)
      norm_num [accepted, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)] at hzero
      linarith
    have h := oneThird_overlap_of_uniform_cube_gap Q.boolEval δ hδ hδ1
      (fun t z i => by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using cube_source_gap hgap Q z i)
    simp only [Fintype.card_fin] at h
    convert h using 1
    congr 1
    exact Subsingleton.elim _ _

/-- Exact quantifier order of the fixed-degree main theorem, relative only
to the explicitly named KS input. The same positive rate works for every
seed length, output length, and coordinate polynomial map of this degree. -/
theorem polynomial_oneThird_exponential (d : ℕ) (hKS : KSOneThirdInput d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s N : ℕ) (Q : Source s N d),
      CubeTilt.overlap Q.boolEval (bernoulliProduct (1/3)) ≤
        Real.exp (-(c * (N : ℝ))) := by
  obtain ⟨δ, hδ, hgap⟩ := hKS
  exact ⟨δ^6, by positivity, fun s N Q => polynomial_oneThird_overlap Q δ hδ hgap⟩

/-- Any uniform acceptance gap gives exponential separation from its product
distribution. The KS non-dyadic theorem provides the displayed input when
`p` is a fixed non-dyadic number in `(0,1)`. -/
theorem polynomial_product_exponential (d : ℕ) (p δ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ)
    (hgap : UniformAcceptanceGap d p δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s N : ℕ) (Q : Source s N d),
      CubeTilt.overlap Q.boolEval (bernoulliProduct p) ≤
        Real.exp (-(c * (N : ℝ))) := by
  have hδp : δ ≤ p := by
    have hz := hgap 0 0 (by simp)
    simpa [accepted, abs_of_nonneg hp.le] using hz
  obtain ⟨t, _, hlo, _⟩ := exists_dyadic_cube_size hδ (hδp.trans hp1.le)
  let K : ℝ := (2 : ℝ)^t
  have hK : 0 < K := by dsimp [K]; positivity
  have hvar : 0 < δ^2 - p*(1-p)/K := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hK).mpr
    dsimp [K]
    nlinarith [sq_nonneg (p-1/2)]
  have hm : 0 < max p (1-p) := hp.trans_le (le_max_left _ _)
  refine ⟨amplificationRate (max p (1-p)) K δ (p*(1-p)), ?_, ?_⟩
  · unfold amplificationRate
    exact mul_pos (div_pos (by norm_num) (mul_pos (sq_pos_of_pos hm) hK))
      (sq_pos_of_pos hvar)
  · intro s N Q
    by_cases hN : N = 0
    · subst N
      simpa using CubeTilt.overlap_le_one Q.boolEval (bernoulliProduct p)
    · letI : NeZero N := ⟨hN⟩
      have h := overlap_bound_of_cube_gap t Q.boolEval p δ hp hp1 hδ.le
        (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hvar)
        (fun z i => by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          cube_source_gap hgap Q z i)
      simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h
      convert h using 1
      congr 1
      exact Subsingleton.elim _ _

/-- The explicit quadratic exponent, relative to the recorded quadratic
acceptance-gap theorem. -/
theorem polynomial_quadratic_overlap {s N : ℕ} (Q : Source s N 2)
    (hgap : PublishedQuadraticGap) :
    CubeTilt.overlap Q.boolEval (bernoulliProduct (1/3)) ≤
      Real.exp (-((1/(2:ℝ)^26) * (N:ℝ))) := by
  by_cases hN : N = 0
  · subst N
    simpa using CubeTilt.overlap_le_one Q.boolEval (bernoulliProduct (1/3))
  · letI : NeZero N := ⟨hN⟩
    have h := overlap_bound_of_cube_gap 9 Q.boolEval (1/3) (1/24)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun z i => by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        cube_source_gap hgap Q z i)
    have hK : ((2^9 : ℕ):ℝ) = 512 := by norm_num
    have hm : max (1/3 : ℝ) (1-1/3) = 2/3 := by norm_num
    rw [hK, hm, oneThird_quadratic_rate] at h
    simp only [Fintype.card_fin] at h
    convert h using 1
    congr 1
    exact Subsingleton.elim _ _

end SamplingLowerBounds
