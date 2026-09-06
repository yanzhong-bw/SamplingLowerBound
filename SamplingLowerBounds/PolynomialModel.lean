import SamplingLowerBounds.Cube
import SamplingLowerBounds.CubeTilt
import SamplingLowerBounds.BernoulliTests
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Boolean polynomials and affine restrictions

The degree notion here is the usual total degree of a multivariate polynomial
over `ZMod 2`. Closure under affine restriction is proved from monomial
expansion; it is not part of the definition of degree.

The acceptance-gap hypothesis is explicitly named and remains a hypothesis:
this module does not purport to formalize the external KS gap theorem.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds
namespace PolynomialModel

noncomputable section

abbrev F₂ := ZMod 2
abbrev Polynomial (σ : Type*) := MvPolynomial σ F₂

section Substitution
variable {σ τ R : Type*} [CommSemiring R]

/-- Substituting degree-at-most-one polynomials never increases total degree. -/
theorem totalDegree_affine_substitution (p : MvPolynomial σ R)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (MvPolynomial.eval₂ MvPolynomial.C f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  calc
    _ ≤ (MvPolynomial.C (MvPolynomial.coeff m p)).totalDegree +
        (m.prod fun i e => f i ^ e).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (m.prod fun i e => f i ^ e).totalDegree := by simp
    _ ≤ ∑ i ∈ m.support, (f i ^ m i).totalDegree :=
      MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hm

variable [Fintype τ]

/-- The polynomial representing a single affine coordinate. -/
def affineForm (a : R) (h : τ → R) : MvPolynomial τ R :=
  MvPolynomial.C a + ∑ j, MvPolynomial.C (h j) * MvPolynomial.X j

theorem affineForm_totalDegree [Nontrivial R] (a : R) (h : τ → R) :
    (affineForm a h).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem eval_affineForm (a : R) (h y : τ → R) :
    MvPolynomial.eval y (affineForm a h) = a + ∑ j, h j * y j := by
  simp [affineForm]

/-- Substitute the affine map `y ↦ x + ∑ j, y j • h j` in a polynomial. -/
def affineRestriction (p : MvPolynomial σ R) (x : σ → R)
    (h : τ → σ → R) : MvPolynomial τ R :=
  MvPolynomial.eval₂ MvPolynomial.C (fun i => affineForm (x i) (fun j => h j i)) p

theorem affineRestriction_totalDegree [Nontrivial R]
    (p : MvPolynomial σ R) (x : σ → R) (h : τ → σ → R) :
    (affineRestriction p x h).totalDegree ≤ p.totalDegree :=
  totalDegree_affine_substitution p _ (fun i => affineForm_totalDegree (x i) (fun j => h j i))

theorem eval_affineRestriction (p : MvPolynomial σ R) (x : σ → R)
    (h : τ → σ → R) (y : τ → R) :
    MvPolynomial.eval y (affineRestriction p x h) =
      MvPolynomial.eval (fun i => x i + ∑ j, h j i * y j) p := by
  exact (MvPolynomial.eval_assoc (fun i => affineForm (x i) (fun j => h j i)) y p).symm.trans
    (by simp [Function.comp_def, eval_affineForm])

end Substitution

/-- A polynomial source: every output coordinate is an actual polynomial over F₂. -/
structure Source (s N d : ℕ) where
  coordinate : Fin N → Polynomial (Fin s)
  degree_le : ∀ i, (coordinate i).totalDegree ≤ d

def Source.eval {s N d : ℕ} (Q : Source s N d) (x : Fin s → F₂) : Fin N → F₂ :=
  fun i => MvPolynomial.eval x (Q.coordinate i)

/-- The real-valued acceptance indicator of a Boolean polynomial. -/
noncomputable def accepted {σ : Type*} (p : Polynomial σ) (x : σ → F₂) : ℝ :=
  if MvPolynomial.eval x p = 1 then 1 else 0

/-- The precisely stated external acceptance-probability gap, uniform over
the number of variables. No instance or axiom asserting this property is given. -/
def UniformAcceptanceGap (d : ℕ) (p δ : ℝ) : Prop :=
  ∀ (s : ℕ) (q : Polynomial (Fin s)), q.totalDegree ≤ d →
    δ ≤ |(𝔼 x : Fin s → F₂, accepted q x) - p|

/-- Applying a uniform polynomial acceptance gap to an arbitrary affine map.
The directions may be linearly dependent and may include zero directions. -/
theorem affine_mean_gap {s t d : ℕ} {p δ : ℝ}
    (hgap : UniformAcceptanceGap d p δ) (q : Polynomial (Fin s))
    (hq : q.totalDegree ≤ d) (x : Fin s → F₂) (h : Fin t → Fin s → F₂) :
    δ ≤ |(𝔼 y : Fin t → F₂,
      accepted q (fun i => x i + ∑ j, h j i * y j)) - p| := by
  have hrestrict := hgap t (affineRestriction q x h)
    ((affineRestriction_totalDegree q x h).trans hq)
  simpa only [accepted, eval_affineRestriction] using hrestrict

/-- Recursive cube tuples and the usual `Fin t` vectors index the same labels. -/
def tupleEquivFun (α : Type*) : (t : ℕ) → Cube.Tuple α t ≃ (Fin t → α)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by funext i; exact Fin.elim0 i }
  | t + 1 =>
    (Equiv.prodCongr (Equiv.refl α) (tupleEquivFun α t)).trans
      (Fin.consEquiv (fun _ => α))

/-- The conventional identification of a Boolean bit with an element of F₂. -/
def boolEquivF₂ : Bool ≃ F₂ where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv b := by cases b <;> decide
  right_inv z := by fin_cases z <;> decide

/-- Boolean labels as the uniformly distributed F₂ input to the restricted polynomial. -/
def labelEquiv (t : ℕ) : Cube.Tuple Bool t ≃ (Fin t → F₂) :=
  (tupleEquivFun Bool t).trans (Equiv.piCongrRight (fun _ => boolEquivF₂))

/-- The recursive affine cube parametrization agrees with the usual affine map. -/
theorem vertex_eq_affine {s : ℕ} (t : ℕ)
    (h : Cube.Tuple (Fin s → F₂) t) (x : Fin s → F₂) (v : Cube.Tuple Bool t) :
    Cube.vertex t h x v = fun i => x i + ∑ j,
      (tupleEquivFun (Fin s → F₂) t h j i) * (labelEquiv t v j) := by
  induction t generalizing x with
  | zero => simp [Cube.vertex]
  | succ t ih =>
    obtain ⟨h₀, h⟩ := h
    obtain ⟨b, v⟩ := v
    rw [Cube.vertex, ih]
    funext i
    cases b <;>
      simp [Fin.sum_univ_succ, tupleEquivFun, labelEquiv, boolEquivF₂,
        Fin.consEquiv, Equiv.prodCongr, Equiv.refl, add_assoc]

/-- A uniform acceptance gap therefore holds on every actual recursively
parametrized cube, with no injectivity assumption on its affine parametrization. -/
theorem cube_mean_gap {s t d : ℕ} {p δ : ℝ}
    (hgap : UniformAcceptanceGap d p δ) (q : Polynomial (Fin s))
    (hq : q.totalDegree ≤ d) (x : Fin s → F₂)
    (h : Cube.Tuple (Fin s → F₂) t) :
    δ ≤ |(𝔼 v : Cube.Tuple Bool t, accepted q (Cube.vertex t h x v)) - p| := by
  have heq : (𝔼 v : Cube.Tuple Bool t, accepted q (Cube.vertex t h x v)) =
      𝔼 y : Fin t → F₂, accepted q (fun i => x i + ∑ j,
        tupleEquivFun (Fin s → F₂) t h j i * y j) := by
    apply Fintype.expect_equiv (labelEquiv t)
    intro v
    rw [vertex_eq_affine]
  rw [heq]
  exact affine_mean_gap hgap q hq x _

/-- Boolean output encoding of the polynomial source; equality with one is
the usual identification because F₂ has exactly the elements zero and one. -/
def Source.boolEval {s N d : ℕ} (Q : Source s N d) (x : Fin s → F₂) : Fin N → Bool :=
  fun i => decide (Q.eval x i = 1)

theorem bitValue_source_eval {s N d : ℕ} (Q : Source s N d)
    (x : Fin s → F₂) (i : Fin N) :
    Information.bitValue (Q.boolEval x i) = accepted (Q.coordinate i) x := by
  simp [Information.bitValue, Source.boolEval, Source.eval, accepted]

/-- The exact deterministic cube-gap input required by the amplification
theorem, now derived for an actual polynomial source from the KS input. -/
theorem cube_source_gap {s N d t : ℕ} {p δ : ℝ}
    (hgap : UniformAcceptanceGap d p δ) (Q : Source s N d)
    (z : CubeTilt.Parameters (Fin s → F₂) t) (i : Fin N) :
    δ ≤ |(∑ v : Cube.Tuple Bool t,
      Information.bitValue (CubeTilt.vertexOutput t Q.boolEval v z i)) /
        (2 ^ t : ℝ) - p| := by
  have hg := cube_mean_gap hgap (Q.coordinate i) (Q.degree_le i) z.2 z.1
  simpa only [Fintype.expect_eq_sum_div_card, Cube.card_vertices, Nat.cast_pow,
    Nat.cast_ofNat, CubeTilt.vertexOutput, bitValue_source_eval] using hg

end
end PolynomialModel
end SamplingLowerBounds
