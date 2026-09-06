import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Real.Basic

/-!
# Weighted affine-cube lower bound

The cube parameter and vertex types are recursively represented tuples. A tuple of
`t` directions and a base point parametrize all affine Boolean cubes, including
those with repeated or dependent directions. The theorem holds over every finite
additive commutative group, and in particular over `Fin s → ZMod 2`.

The proof below uses no results about polynomial acceptance probabilities or
information-theoretic estimates.
-/

open scoped BigOperators

namespace SamplingLowerBounds
namespace Cube

universe u

/-- A recursively represented tuple of length `t`. -/
def Tuple (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | t + 1 => α × Tuple α t

instance tupleFintype {α : Type*} [Fintype α] (t : ℕ) : Fintype (Tuple α t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ t ih =>
    letI := ih
    exact inferInstanceAs (Fintype (α × Tuple α t))

instance tupleNonempty {α : Type*} [Nonempty α] (t : ℕ) : Nonempty (Tuple α t) := by
  induction t with
  | zero => exact inferInstanceAs (Nonempty PUnit)
  | succ t ih =>
    letI := ih
    exact inferInstanceAs (Nonempty (α × Tuple α t))

lemma card_tuple {α : Type*} [Fintype α] (t : ℕ) :
    Fintype.card (Tuple α t) = Fintype.card α ^ t := by
  induction t with
  | zero => simp [Tuple]
  | succ t ih => simp [Tuple, ih, pow_succ, Nat.mul_comm]

@[simp] lemma card_vertices (t : ℕ) : Fintype.card (Tuple Bool t) = 2 ^ t := by
  simp [card_tuple]

section Average
variable {α : Type*} [Fintype α] [Nonempty α]

/-- Cauchy--Schwarz with one factor equal to one. -/
lemma mean_sq_le (f : α → ℝ) : (𝔼 x, f x) ^ 2 ≤ 𝔼 x, f x ^ 2 := by
  simpa using Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ => (1 : ℝ))

/-- The powers-of-two case of finite Jensen, proved by repeated Cauchy--Schwarz. -/
lemma mean_pow_two_le (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (t : ℕ) :
    (𝔼 x, f x) ^ (2 ^ t) ≤ 𝔼 x, f x ^ (2 ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hnonneg : 0 ≤ (𝔼 x, f x) ^ (2 ^ t) :=
      pow_nonneg (Finset.expect_nonneg (fun x _ => hf x)) _
    calc
      (𝔼 x, f x) ^ (2 ^ (t + 1)) = ((𝔼 x, f x) ^ (2 ^ t)) ^ 2 := by
        rw [pow_succ, pow_mul]
      _ ≤ (𝔼 x, f x ^ (2 ^ t)) ^ 2 := pow_le_pow_left₀ hnonneg ih 2
      _ ≤ 𝔼 x, (f x ^ (2 ^ t)) ^ 2 := mean_sq_le _
      _ = 𝔼 x, f x ^ (2 ^ (t + 1)) := by simp only [Nat.pow_succ, pow_mul]

end Average

section Group
variable {G : Type*} [AddCommGroup G]

/-- The vertex indexed by a Boolean tuple. -/
def vertex : (t : ℕ) → Tuple G t → G → Tuple Bool t → G
  | 0, _, x, _ => x
  | t + 1, (h, hs), x, (b, bs) => vertex t hs (x + if b then h else 0) bs

lemma vertex_translate (t : ℕ) (hs : Tuple G t) (x a : G) (v : Tuple Bool t) :
    vertex t hs (x + a) v = vertex t hs x v + a := by
  induction t generalizing x a with
  | zero => rfl
  | succ t ih =>
    obtain ⟨h, hs⟩ := hs
    obtain ⟨b, bs⟩ := v
    simp only [vertex]
    rw [show x + a + (if b then h else 0) = (x + (if b then h else 0)) + a by simp [add_assoc, add_comm, add_left_comm]]
    exact ih hs (x + if b then h else 0) a bs

/-- Product of the weights of every labelled vertex; multiplicities are retained. -/
noncomputable def weight (t : ℕ) (f : G → ℝ) (hs : Tuple G t) (x : G) : ℝ :=
  ∏ v : Tuple Bool t, f (vertex t hs x v)

@[simp] lemma weight_zero (f : G → ℝ) (hs : Tuple G 0) (x : G) :
    weight 0 f hs x = f x := by simp [weight, Tuple, vertex]

/-- Splitting the first Boolean coordinate is exactly multiplicative differencing. -/
lemma weight_succ (t : ℕ) (f : G → ℝ) (h : G) (hs : Tuple G t) (x : G) :
    weight (t + 1) f (h, hs) x = weight t (fun z => f z * f (z + h)) hs x := by
  simp only [weight, Tuple, Fintype.prod_prod_type, Fintype.prod_bool, vertex,
    Bool.false_eq_true, ↓reduceIte, add_zero, vertex_translate]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  exact mul_comm _ _

variable [Fintype G]

/-- Mean weight of a uniformly parametrized affine cube. -/
noncomputable def meanWeight (t : ℕ) (f : G → ℝ) : ℝ :=
  𝔼 hs : Tuple G t, 𝔼 x : G, weight t f hs x

@[simp] lemma meanWeight_zero (f : G → ℝ) : meanWeight 0 f = 𝔼 x, f x := by
  simp [meanWeight, Tuple]

lemma meanWeight_succ (t : ℕ) (f : G → ℝ) :
    meanWeight (t + 1) f = 𝔼 h, meanWeight t (fun z => f z * f (z + h)) := by
  change (𝔼 hs : G × Tuple G t, 𝔼 x : G, weight (t + 1) f hs x) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp_rw [weight_succ]
  rfl

/-- Translation of uniform measure, proved by the addition bijection. -/
lemma mean_translate (f : G → ℝ) (x : G) : (𝔼 h, f (x + h)) = 𝔼 h, f h := by
  apply Fintype.expect_bijective (fun h : G => x + h)
    ⟨fun a b h => add_left_cancel h, fun y => ⟨-x + y, by simp [add_assoc, add_comm, add_left_comm]⟩⟩
  intro h
  rfl

/-- The two endpoints of a uniformly parametrized one-dimensional cube are independent. -/
lemma mean_correlation (f : G → ℝ) :
    (𝔼 h, 𝔼 x, f x * f (x + h)) = (𝔼 x, f x) ^ 2 := by
  rw [Finset.expect_comm]
  simp_rw [← Finset.mul_expect, mean_translate]
  rw [← Finset.expect_mul]
  rw [pow_two]

/-- Weighted affine-cube lower bound, including the zero-dimensional base case.

No rank or distinctness condition is imposed on the sampled directions. Nonnegative
weights suffice; the paper's additional upper bound `f ≤ 1` is not needed here.
-/
theorem weighted_affine_cube_lower_bound (t : ℕ) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, f x) ^ (2 ^ t) ≤ meanWeight t f := by
  induction t generalizing f with
  | zero => simp
  | succ t ih =>
    rw [meanWeight_succ]
    have hcor (h : G) : 0 ≤ 𝔼 x, f x * f (x + h) :=
      Finset.expect_nonneg (fun x _ => mul_nonneg (hf x) (hf (x + h)))
    calc
      (𝔼 x, f x) ^ (2 ^ (t + 1)) =
          ((𝔼 x, f x) ^ 2) ^ (2 ^ t) := by rw [← pow_mul, pow_succ, Nat.mul_comm]
      _ = (𝔼 h, 𝔼 x, f x * f (x + h)) ^ (2 ^ t) := by rw [mean_correlation]
      _ ≤ 𝔼 h, (𝔼 x, f x * f (x + h)) ^ (2 ^ t) := mean_pow_two_le _ hcor t
      _ ≤ 𝔼 h, meanWeight t (fun z => f z * f (z + h)) :=
        Finset.expect_le_expect (fun h _ => ih _ (fun z => mul_nonneg (hf z) (hf (z + h))))

/-- A positive mean weight gives a strictly positive cube normalizing constant. -/
lemma meanWeight_pos (t : ℕ) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hmean : 0 < 𝔼 x, f x) : 0 < meanWeight t f :=
  lt_of_lt_of_le (pow_pos hmean _) (weighted_affine_cube_lower_bound t f hf)

/-- The normalizing constant is at most one for weights in the unit interval. -/
lemma meanWeight_le_one (t : ℕ) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) : meanWeight t f ≤ 1 := by
  apply Finset.expect_le Finset.univ_nonempty
  intro hs _
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  apply Finset.prod_le_one
  · intro v _
    exact hf _
  · intro v _
    exact hf_one _

end Group
end Cube
end SamplingLowerBounds
