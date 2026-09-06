import SamplingLowerBounds.Cube
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

/-!
# Pairwise independence after conditioning the other cube directions

The map `(x,h) ↦ (x+a,x+h+b)` is a permutation of two copies of an
additive commutative group. Consequently the two components are independent
uniform points. Boolean labels which differ on the selected direction reduce
to this map or its coordinate swap, whatever the remaining directions are.

The final theorem carries this calculation through the recursive tuple
representation of affine cubes, proving pairwise independence for every two
distinct labels in every dimension, including cubes with repeated vertices.
-/

open scoped BigOperators

namespace SamplingLowerBounds
namespace AffinePair

variable {G : Type*} [AddCommGroup G]

/-- The affine two-vertex parametrization is an equivalence, without any rank
assumption on other, already fixed cube directions. -/
def affinePairEquiv (a b : G) : G × G ≃ G × G where
  toFun z := (z.1 + a, z.1 + z.2 + b)
  invFun z := (z.1 - a, z.2 - (z.1 - a) - b)
  left_inv z := by ext <;> dsimp <;> abel
  right_inv z := by ext <;> dsimp <;> abel

theorem affinePair_bijective (a b : G) :
    Function.Bijective (fun z : G × G => (z.1 + a, z.1 + z.2 + b)) :=
  (affinePairEquiv a b).bijective

variable [Fintype G]

/-- Every test on the affine pair has the same average as its uniform pair
average; this identifies the entire joint law, not merely a correlation. -/
theorem affinePair_expect (a b : G) (H : G × G → ℝ) :
    (𝔼 z : G × G, H (z.1 + a, z.1 + z.2 + b)) = 𝔼 z : G × G, H z := by
  exact Fintype.expect_equiv (affinePairEquiv a b) _ _ (fun _ => rfl)

/-- The two affine vertices are independent uniform points. -/
theorem affinePair_factor (a b : G) (F H : G → ℝ) :
    (𝔼 z : G × G, F (z.1 + a) * H (z.1 + z.2 + b)) =
      (𝔼 x : G, F x) * (𝔼 y : G, H y) := by
  rw [affinePair_expect a b (fun z => F z.1 * H z.2)]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp_rw [← Finset.mul_expect]
  rw [← Finset.expect_mul]

/-- The equivalent iterated-average formulation permits conditioning on other
random cube directions before applying the affine-pair identity. -/
theorem affinePair_factor_iterated (a b : G) (F H : G → ℝ) :
    (𝔼 x : G, 𝔼 h : G, F (x + a) * H (x + h + b)) =
      (𝔼 x : G, F x) * (𝔼 y : G, H y) := by
  rw [← Finset.expect_product', Finset.univ_product_univ]
  exact affinePair_factor a b F H

/-- If two Boolean labels differ on one direction, their conditional joint law
is uniform, regardless of the contributions `a,b` from the other directions. -/
theorem differing_bits_factor (u v : Bool) (huv : u ≠ v) (a b : G) (F H : G → ℝ) :
    (𝔼 z : G × G,
      F (z.1 + (if u then z.2 else 0) + a) *
      H (z.1 + (if v then z.2 else 0) + b)) =
      (𝔼 x : G, F x) * (𝔼 y : G, H y) := by
  cases u <;> cases v
  · exact (huv rfl).elim
  · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      affinePair_factor a b F H
  · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, mul_comm] using
      affinePair_factor b a H F
  · exact (huv rfl).elim

omit [Fintype G] in
/-- A cube vertex is the base point plus an offset fixed by the directions. -/
theorem vertex_as_offset (t : ℕ) (hs : Cube.Tuple G t) (x : G)
    (v : Cube.Tuple Bool t) :
    Cube.vertex t hs x v = x + Cube.vertex t hs 0 v := by
  simpa only [zero_add, add_zero, add_comm] using Cube.vertex_translate t hs 0 x v

/-- Every cube vertex is uniform, even after all directions have been fixed. -/
theorem cube_vertex_expect (t : ℕ) (hs : Cube.Tuple G t)
    (v : Cube.Tuple Bool t) (F : G → ℝ) :
    (𝔼 x : G, F (Cube.vertex t hs x v)) = 𝔼 x : G, F x := by
  calc
    _ = 𝔼 x : G, F (x + Cube.vertex t hs 0 v) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [vertex_as_offset t hs x v]
    _ = _ := by
      simpa only [add_comm] using Cube.mean_translate F (Cube.vertex t hs 0 v)

/-- The one-vertex marginal of the uniform cube is uniform. -/
theorem cube_single_expect (t : ℕ) (v : Cube.Tuple Bool t) (F : G → ℝ) :
    (𝔼 hs : Cube.Tuple G t, 𝔼 x : G, F (Cube.vertex t hs x v)) =
      𝔼 x : G, F x := by
  simp_rw [cube_vertex_expect]
  simp

/-- Averaging over the base point removes any common translation. -/
theorem shifted_cube_pair (t : ℕ) (hs : Cube.Tuple G t) (a : G)
    (v w : Cube.Tuple Bool t) (F H : G → ℝ) :
    (𝔼 x : G, F (Cube.vertex t hs (x + a) v) * H (Cube.vertex t hs (x + a) w)) =
      𝔼 x : G, F (Cube.vertex t hs x v) * H (Cube.vertex t hs x w) := by
  simpa only [add_comm] using
    Cube.mean_translate (fun x => F (Cube.vertex t hs x v) * H (Cube.vertex t hs x w)) a

/-- On a direction where the labels differ, averaging the direction and base
point gives the product mean for each fixed choice of all remaining directions. -/
theorem conditioned_cube_pair (t : ℕ) (hs : Cube.Tuple G t)
    (u u' : Bool) (hu : u ≠ u') (v w : Cube.Tuple Bool t) (F H : G → ℝ) :
    (𝔼 h : G, 𝔼 x : G,
      F (Cube.vertex t hs (x + if u then h else 0) v) *
      H (Cube.vertex t hs (x + if u' then h else 0) w)) =
      (𝔼 x : G, F x) * (𝔼 y : G, H y) := by
  calc
    _ = (𝔼 h : G, 𝔼 x : G,
        F ((x + if u then h else 0) + Cube.vertex t hs 0 v) *
        H ((x + if u' then h else 0) + Cube.vertex t hs 0 w)) := by
      apply Finset.expect_congr rfl
      intro h _
      apply Finset.expect_congr rfl
      intro x _
      rw [vertex_as_offset t hs (x + if u then h else 0) v,
        vertex_as_offset t hs (x + if u' then h else 0) w]
    _ = _ := by
      rw [Finset.expect_comm, ← Finset.expect_product', Finset.univ_product_univ]
      exact differing_bits_factor u u' hu (Cube.vertex t hs 0 v) (Cube.vertex t hs 0 w) F H

/-- Distinct labelled vertices of a uniformly parametrized affine cube are
independent uniform points. Directions need not be linearly independent.

The statement holds over any finite additive commutative group, so applies in
particular to the Boolean seed group. The independent quantities are the random
variables indexed by distinct labels, even though individual realized cubes can
have repeated vertices.
-/
theorem cube_pair_factor (t : ℕ) (F H : G → ℝ)
    (v w : Cube.Tuple Bool t) (hvw : v ≠ w) :
    (𝔼 hs : Cube.Tuple G t, 𝔼 x : G,
      F (Cube.vertex t hs x v) * H (Cube.vertex t hs x w)) =
      (𝔼 x : G, F x) * (𝔼 y : G, H y) := by
  induction t with
  | zero =>
    cases v
    cases w
    exact (hvw rfl).elim
  | succ t ih =>
    obtain ⟨u, v⟩ := v
    obtain ⟨u', w⟩ := w
    change (𝔼 hs : G × Cube.Tuple G t, 𝔼 x : G,
      F (Cube.vertex (t + 1) hs x (u, v)) *
      H (Cube.vertex (t + 1) hs x (u', w))) = _
    rw [← Finset.univ_product_univ, Finset.expect_product]
    change (𝔼 h : G, 𝔼 hs : Cube.Tuple G t, 𝔼 x : G,
      F (Cube.vertex t hs (x + if u then h else 0) v) *
      H (Cube.vertex t hs (x + if u' then h else 0) w)) = _
    by_cases hu : u = u'
    · subst u'
      have htail : v ≠ w := fun heq => hvw (Prod.ext rfl heq)
      simp_rw [shifted_cube_pair]
      rw [ih v w htail]
      simp
    · rw [Finset.expect_comm]
      simp_rw [conditioned_cube_pair t _ u u' hu v w F H]
      simp

/-- Event probabilities at any two distinct cube labels factor. -/
theorem cube_pair_events (t : ℕ) (v w : Cube.Tuple Bool t) (hvw : v ≠ w)
    (A B : G → Prop) [DecidablePred A] [DecidablePred B] :
    (𝔼 hs : Cube.Tuple G t, 𝔼 x : G,
      if A (Cube.vertex t hs x v) ∧ B (Cube.vertex t hs x w) then (1 : ℝ) else 0) =
      (𝔼 x : G, if A x then (1 : ℝ) else 0) *
      (𝔼 y : G, if B y then (1 : ℝ) else 0) := by
  have h := cube_pair_factor t (fun x => if A x then (1 : ℝ) else 0)
    (fun y => if B y then (1 : ℝ) else 0) v w hvw
  have indicator_mul (x y : G) :
      (if A x then (1 : ℝ) else 0) * (if B y then (1 : ℝ) else 0) =
        if A x ∧ B y then (1 : ℝ) else 0 := by
    by_cases hA : A x <;> by_cases hB : B y <;> simp [hA, hB]
  simpa only [indicator_mul] using h

end AffinePair
end SamplingLowerBounds
