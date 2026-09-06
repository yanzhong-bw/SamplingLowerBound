import SamplingLowerBounds.PolynomialModel
import SamplingLowerBounds.FlatGraph

/-! # Coordinate projection of actual polynomial sources -/

open Classical

namespace SamplingLowerBounds.PolynomialModel

/-- Selecting output coordinates preserves the polynomial degree, with repetitions allowed. -/
def Source.project {s N d q : ℕ} (Q : Source s N d) (f : Fin q → Fin N) : Source s q d where
  coordinate i := Q.coordinate (f i)
  degree_le i := Q.degree_le (f i)

theorem Source.project_boolEval {s N d q : ℕ} (Q : Source s N d)
    (f : Fin q → Fin N) (x : Fin s → F₂) :
    (Q.project f).boolEval x = fun i => Q.boolEval x (f i) := rfl

theorem outputLaw_eq_pushMass {G A : Type*} [AddCommGroup G] [Fintype G] [Fintype A]
    (Q : G → A) :
    CubeTilt.outputLaw Q = Information.pushMass (CubeTilt.uniformMass G) Q := rfl

theorem outputLaw_postprocess {G A B : Type*} [AddCommGroup G]
    [Fintype G] [Fintype A] [Fintype B] (Q : G → A) (f : A → B) :
    Information.pushMass (CubeTilt.outputLaw Q) f = CubeTilt.outputLaw (f ∘ Q) := by
  rw [outputLaw_eq_pushMass, outputLaw_eq_pushMass]
  funext b
  exact FlatGraph.pushMass_comp _ _ _ _

/-- The actual law after projecting output bits is the law of the projected source. -/
theorem Source.project_outputLaw {s N d q : ℕ} (Q : Source s N d)
    (f : Fin q → Fin N) :
    Information.pushMass (CubeTilt.outputLaw Q.boolEval) (fun y i => y (f i)) =
      CubeTilt.outputLaw (Q.project f).boolEval :=
  outputLaw_postprocess Q.boolEval _

end SamplingLowerBounds.PolynomialModel
