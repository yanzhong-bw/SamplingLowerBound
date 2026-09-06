import SamplingLowerBounds.CoordinateEncoding
import SamplingLowerBounds.PolynomialSampling

/-!
# Translating polynomial sources and target distributions

XOR with a fixed output vector is an explicit bijection. Adding the
corresponding constants to the coordinate polynomials preserves degree.
Consequently a bound uniform over polynomial sources transfers to every
translate of the target distribution.
-/

open Classical

namespace SamplingLowerBounds
namespace PolynomialModel

/-- Translation by a fixed Boolean vector, with itself as inverse. -/
def xorVectorEquiv {ι : Type*} (b : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun y := fun i => Bool.xor (y i) (b i)
  invFun y := fun i => Bool.xor (y i) (b i)
  left_inv y := by
    funext i
    change Bool.xor (Bool.xor (y i) (b i)) (b i) = y i
    cases y i <;> cases b i <;> rfl
  right_inv y := by
    funext i
    change Bool.xor (Bool.xor (y i) (b i)) (b i) = y i
    cases y i <;> cases b i <;> rfl

theorem xorVectorEquiv_twice {ι : Type*} (b y : ι → Bool) :
    xorVectorEquiv b (xorVectorEquiv b y) = y := (xorVectorEquiv b).left_inv y

theorem pushMass_xor_twice {ι : Type*} [Fintype (ι → Bool)]
    (M : (ι → Bool) → ℝ) (b : ι → Bool) :
    Information.pushMass (Information.pushMass M (xorVectorEquiv b)) (xorVectorEquiv b) = M := by
  funext y
  rw [FlatGraph.pushMass_comp]
  simp [Information.pushMass, Function.comp_def, xorVectorEquiv_twice]

/-- Adding constants to output polynomials realizes an XOR translation
while preserving the given degree bound. -/
noncomputable def Source.translate {s N d : ℕ} (Q : Source s N d) (b : Fin N → Bool) :
    Source s N d where
  coordinate i := Q.coordinate i + MvPolynomial.C (boolEquivF₂ (b i))
  degree_le i := (MvPolynomial.totalDegree_add _ _).trans
    (max_le (Q.degree_le i) (by simp))

theorem f₂_add_bit_eq_xor (a : F₂) (b : Bool) :
    decide (a + boolEquivF₂ b = 1) = Bool.xor (decide (a = 1)) b := by
  fin_cases a <;> cases b <;> decide

theorem Source.translate_boolEval {s N d : ℕ} (Q : Source s N d)
    (b : Fin N → Bool) (x : Fin s → F₂) :
    (Q.translate b).boolEval x = xorVectorEquiv b (Q.boolEval x) := by
  funext i
  simp only [Source.boolEval, Source.eval, Source.translate, map_add, MvPolynomial.eval_C]
  exact f₂_add_bit_eq_xor _ _

theorem Source.translate_outputLaw {s N d : ℕ} (Q : Source s N d) (b : Fin N → Bool) :
    Information.pushMass (CubeTilt.outputLaw Q.boolEval) (xorVectorEquiv b) =
      CubeTilt.outputLaw (Q.translate b).boolEval := by
  rw [outputLaw_postprocess]
  have heval : xorVectorEquiv b ∘ Q.boolEval = (Q.translate b).boolEval := by
    funext x
    exact (Q.translate_boolEval b x).symm
  rw [heval]

/-- Moving the fixed XOR translation from the target law to the source
preserves the overlap exactly. -/
theorem Source.overlap_translated_target {s N d : ℕ} (Q : Source s N d)
    (b : Fin N → Bool) (M : (Fin N → Bool) → ℝ) :
    CubeTilt.overlap Q.boolEval (Information.pushMass M (xorVectorEquiv b)) =
      CubeTilt.overlap (Q.translate b).boolEval M := by
  have h := FlatGraph.massOverlap_equiv (CubeTilt.outputLaw Q.boolEval)
    (Information.pushMass M (xorVectorEquiv b)) (xorVectorEquiv b)
  rw [Q.translate_outputLaw] at h
  rw [pushMass_xor_twice M b] at h
  exact h.symm

end PolynomialModel

open PolynomialModel

/-- Any lower bound uniform over degree-`d` sources also holds for all XOR
translates of its target distribution. -/
theorem polynomial_translated_target_bound {s N d : ℕ}
    (M : (Fin N → Bool) → ℝ) (B : ℝ)
    (hbound : ∀ Q : Source s N d, CubeTilt.overlap Q.boolEval M ≤ B)
    (Q : Source s N d) (b : Fin N → Bool) :
    CubeTilt.overlap Q.boolEval (Information.pushMass M (xorVectorEquiv b)) ≤ B := by
  rw [Q.overlap_translated_target]
  exact hbound (Q.translate b)

/-- The paper's explicit quadratic exponent holds for every translated
one-third product target. The published quadratic gap remains an explicit
proof argument, as in the untranslated result. -/
theorem polynomial_quadratic_translated_overlap {s N : ℕ} (Q : Source s N 2)
    (b : Fin N → Bool) (hgap : PublishedQuadraticGap) :
    CubeTilt.overlap Q.boolEval
      (Information.pushMass (bernoulliProduct (1/3)) (xorVectorEquiv b)) ≤
      Real.exp (-((1/(2:ℝ)^26) * (N:ℝ))) := by
  rw [Q.overlap_translated_target]
  exact polynomial_quadratic_overlap (Q.translate b) hgap

end SamplingLowerBounds
