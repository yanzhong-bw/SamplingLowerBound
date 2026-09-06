import SamplingLowerBounds.CoordinateEncoding

/-!
# Optimality of the entropy dependence for every flat target

Both witnesses are actual polynomial sources: a constant map and the identity.
The result applies to every flat normalized target law, not only graph targets.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.PolynomialModel
open Information CubeTilt FlatGraph

noncomputable def constantSource (N d : ℕ) (a : Fin N → Bool) : Source 0 N d where
  coordinate i := MvPolynomial.C (boolEquivF₂ (a i))
  degree_le i := by simp

theorem constantSource_boolEval (N d : ℕ) (a : Fin N → Bool) (x : Fin 0 → F₂) :
    (constantSource N d a).boolEval x = a := by
  funext i
  cases h : a i <;>
    simp [Source.boolEval, Source.eval, constantSource, boolEquivF₂, h]

theorem constantSource_outputLaw (N d : ℕ) (a : Fin N → Bool) :
    outputLaw (constantSource N d a).boolEval = pointMass a := by
  rw [outputLaw_eq_pushMass]
  funext b
  simp only [pushMass, constantSource_boolEval, pointMass]
  split_ifs
  · exact uniformMass_sum _
  · simp

noncomputable def identitySource (N d : ℕ) (hd : 1 ≤ d) : Source N N d where
  coordinate i := MvPolynomial.X i
  degree_le i := by simpa using hd

theorem identitySource_outputLaw (N d : ℕ) (hd : 1 ≤ d) :
    outputLaw (identitySource N d hd).boolEval = uniformMass (Fin N → Bool) := by
  let e : (Fin N → F₂) ≃ (Fin N → Bool) :=
    Equiv.piCongrRight (fun _ => boolEquivF₂.symm)
  have he : (identitySource N d hd).boolEval = e := by
    funext x i
    simp [identitySource, Source.boolEval, Source.eval, e, boolEquivF₂]
  rw [outputLaw_eq_pushMass, he]
  exact uniformMass_equiv e

/-- A normalized flat distribution on N bits cannot have entropy above N. -/
theorem flat_entropy_le_dimension {N k : ℕ} (P : (Fin N → Bool) → ℝ)
    (hPsum : ∑ x, P x = 1) (hflat : ∀ x, P x = 0 ∨ P x = 1/(2:ℝ)^k) : k ≤ N := by
  have hm : (0:ℝ) < 2^k := by positivity
  have hbound : 1 ≤ (2:ℝ)^N/(2:ℝ)^k := by
    calc
      1 = ∑ x, P x := hPsum.symm
      _ ≤ ∑ _x : Fin N → Bool, 1/(2:ℝ)^k := Finset.sum_le_sum fun x _ => by
        rcases hflat x with hx | hx
        · rw [hx]; positivity
        · rw [hx]
      _ = _ := by simp [div_eq_mul_inv]
  have hpowers : (2:ℝ)^k ≤ (2:ℝ)^N := by
    have h := (le_div_iff₀ hm).mp hbound
    simpa using h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hpowers

/-- Exact overlap of the ambient uniform law with an arbitrary flat law. -/
theorem uniform_flat_overlap {N k : ℕ} (P : (Fin N → Bool) → ℝ)
    (hPsum : ∑ x, P x = 1) (hflat : ∀ x, P x = 0 ∨ P x = 1/(2:ℝ)^k) :
    massOverlap (uniformMass (Fin N → Bool)) P = (2:ℝ)^k/(2:ℝ)^N := by
  have hk := flat_entropy_le_dimension P hPsum hflat
  have hm : (0:ℝ)<2^k := by positivity
  have hT : (0:ℝ)<2^N := by positivity
  have hcompare : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^k :=
    one_div_le_one_div_of_le hm ((pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mpr hk)
  have hpoint (x : Fin N → Bool) :
      min (uniformMass (Fin N → Bool) x) (P x) = P x * ((2:ℝ)^k/(2:ℝ)^N) := by
    have hu : uniformMass (Fin N → Bool) x = 1/(2:ℝ)^N := by simp [uniformMass]
    rw [hu]
    rcases hflat x with hx | hx
    · rw [hx, min_eq_right (by positivity), zero_mul]
    · rw [hx, min_eq_left hcompare]
      field_simp
  unfold massOverlap
  simp_rw [hpoint]
  rw [← Finset.sum_mul, hPsum, one_mul]

/-- One of two explicit polynomial samplers has the optimal universal
overlap with an arbitrary flat target: either a constant or the identity. -/
theorem flat_overlap_lower_bound_max {N k d : ℕ} (hd : 1 ≤ d)
    (P : (Fin N → Bool) → ℝ) (hPsum : ∑ x, P x = 1)
    (hflat : ∀ x, P x = 0 ∨ P x = 1/(2:ℝ)^k) :
    ∃ s, ∃ Q : Source s N d,
      max (1/(2:ℝ)^k) ((2:ℝ)^k/(2:ℝ)^N) ≤ overlap Q.boolEval P := by
  have hnonneg : ∀ x, 0 ≤ P x := by
    intro x
    rcases hflat x with hx | hx
    · rw [hx]
    · rw [hx]; positivity
  have hex : ∃ a, P a ≠ 0 := by
    by_contra! h
    have hz : ∑ x, P x = 0 := Finset.sum_eq_zero fun x _ => h x
    linarith
  obtain ⟨a, ha⟩ := hex
  have ha' : P a = 1/(2:ℝ)^k := (hflat a).resolve_left ha
  have hconstant : overlap (constantSource N d a).boolEval P = 1/(2:ℝ)^k := by
    change massOverlap (outputLaw (constantSource N d a).boolEval) P = _
    rw [constantSource_outputLaw, pointMass_overlap a P hnonneg, ha']
    rw [ha']
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have hidentity : overlap (identitySource N d hd).boolEval P = (2:ℝ)^k/(2:ℝ)^N := by
    change massOverlap (outputLaw (identitySource N d hd).boolEval) P = _
    rw [identitySource_outputLaw, uniform_flat_overlap P hPsum hflat]
  by_cases h : 1/(2:ℝ)^k ≤ (2:ℝ)^k/(2:ℝ)^N
  · exact ⟨N, identitySource N d hd, by rw [hidentity, max_eq_right h]⟩
  · exact ⟨0, constantSource N d a, by rw [hconstant, max_eq_left (le_of_not_ge h)]⟩

/-- Entropy dependence is universally optimal up to constant factors in
the exponent, witnessed by degree-at-most-one polynomial sources. -/
theorem flat_overlap_lower_bound {N k d : ℕ} (hd : 1 ≤ d)
    (P : (Fin N → Bool) → ℝ) (hPsum : ∑ x, P x = 1)
    (hflat : ∀ x, P x = 0 ∨ P x = 1/(2:ℝ)^k) :
    ∃ s, ∃ Q : Source s N d,
      1/(2:ℝ)^(min k (N-k)) ≤ overlap Q.boolEval P := by
  obtain ⟨s,Q,hQ⟩ := flat_overlap_lower_bound_max hd P hPsum hflat
  refine ⟨s,Q, ?_⟩
  have hk := flat_entropy_le_dimension P hPsum hflat
  have heq : (2:ℝ)^k/(2:ℝ)^N = 1/(2:ℝ)^(N-k) := by
    rw [← Nat.add_sub_of_le hk, pow_add]
    field_simp
  by_cases h : k ≤ N-k
  · rw [min_eq_left h]
    exact (le_max_left _ _).trans hQ
  · rw [min_eq_right (le_of_not_ge h)]
    rw [heq] at hQ
    exact (le_max_right _ _).trans hQ

end SamplingLowerBounds.PolynomialModel
