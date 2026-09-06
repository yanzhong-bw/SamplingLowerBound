import SamplingLowerBounds.Amplification
import SamplingLowerBounds.CubeTilt
import SamplingLowerBounds.BernoulliTests

/-!
# Exponential overlap bounds for actual cube-separated output maps

The source law, product target, overlap-induced tilt, information budgets,
Pinsker estimates, and second-moment assembly are linked here. The only
structural hypothesis on the output map is its coordinatewise acceptance gap
on every labelled affine cube; no information inequality is assumed.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds

open Information

variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I]

/-- The product Bernoulli target on a finite coordinate set. -/
noncomputable def bernoulliProduct (p : ℝ) : (I → Bool) → ℝ :=
  productMass (fun _ => bernoulliMass p)

theorem bernoulliProduct_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (x : I → Bool) : 0 < bernoulliProduct p x := by
  exact Finset.prod_pos fun i _ => bernoulliMass_pos p hp hp1 (x i)

theorem bernoulliProduct_sum (p : ℝ) : ∑ x : I → Bool, bernoulliProduct p x = 1 := by
  rw [bernoulliProduct, productMass_sum]
  simp_rw [bernoulliMass_sum]
  simp

namespace CubeTilt

theorem singleLaw_expectation (t : ℕ) (Q : G → I → Bool)
    (M : (I → Bool) → ℝ) (v : Cube.Tuple Bool t) (f : (I → Bool) → ℝ) :
    (∑ a, singleLaw t Q M v a * f a) =
      ∑ z, law t Q M z * f (vertexOutput t Q v z) := by
  exact pushMass_expectation (law t Q M) (vertexOutput t Q v) f

theorem pairLaw_expectation (t : ℕ) (Q : G → I → Bool)
    (M : (I → Bool) → ℝ) (v w : Cube.Tuple Bool t)
    (f : ((I → Bool) × (I → Bool)) → ℝ) :
    (∑ ab, pairLaw t Q M v w ab * f ab) =
      ∑ z, law t Q M z * f (vertexOutput t Q v z, vertexOutput t Q w z) := by
  have heq : pairLaw t Q M v w =
      pushMass (law t Q M) (fun z => (vertexOutput t Q v z, vertexOutput t Q w z)) := by
    funext ab
    rcases ab with ⟨a,b⟩
    simp only [pairLaw, finiteEventMass, pushMass, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : vertexOutput t Q v z = a ∧ vertexOutput t Q w z = b
    · simp only [if_pos hz]
    · simp only [if_neg hz]
  rw [heq, pushMass_expectation]

/-- Joint vertex outputs written as a vector of coordinate pairs. -/
noncomputable def pairedCoordinateLaw (t : ℕ) (Q : G → I → Bool)
    (M : (I → Bool) → ℝ) (v w : Cube.Tuple Bool t) (x : I → Bool × Bool) : ℝ :=
  pairLaw t Q M v w (fun i => (x i).1, fun i => (x i).2)

theorem pairedCoordinateLaw_sum (t : ℕ) (Q : G → I → Bool)
    (M : (I → Bool) → ℝ) (hM : ∀ a, 0 ≤ M a) (hω : 0 < overlap Q M)
    (v w : Cube.Tuple Bool t) : ∑ x, pairedCoordinateLaw t Q M v w x = 1 := by
  have he := (Equiv.arrowProdEquivProdArrow I (fun _ => Bool) (fun _ => Bool)).sum_comp
    (pairLaw t Q M v w)
  exact he.trans (pairLaw_sum t Q M hM hω v w)

theorem pairedCoordinateLaw_expectation (t : ℕ) (Q : G → I → Bool)
    (M : (I → Bool) → ℝ) (v w : Cube.Tuple Bool t) (i : I)
    (f : Bool × Bool → ℝ) :
    (∑ x, pairedCoordinateLaw t Q M v w x * f (x i)) =
      ∑ z, law t Q M z * f (vertexOutput t Q v z i, vertexOutput t Q w z i) := by
  have he := (Equiv.arrowProdEquivProdArrow I (fun _ => Bool) (fun _ => Bool)).sum_comp
    (fun ab => pairLaw t Q M v w ab * f (ab.1 i, ab.2 i))
  exact he.trans (pairLaw_expectation t Q M v w (fun ab => f (ab.1 i, ab.2 i)))

theorem pairedCoordinateLaw_KL (t : ℕ) (Q : G → I → Bool)
    (M : (I → Bool) → ℝ) (v w : Cube.Tuple Bool t) (p : ℝ) :
    finiteKL (pairedCoordinateLaw t Q M v w)
      (productMass (fun _ (b : Bool × Bool) => bernoulliMass p b.1 * bernoulliMass p b.2)) =
    finiteKL (pairLaw t Q M v w)
      (fun ab => bernoulliProduct p ab.1 * bernoulliProduct p ab.2) := by
  unfold finiteKL
  apply Fintype.sum_equiv
    (Equiv.arrowProdEquivProdArrow I (fun _ => Bool) (fun _ => Bool))
  intro x
  simp only [pairedCoordinateLaw, productMass, bernoulliProduct,
    Equiv.arrowProdEquivProdArrow_apply, Finset.prod_mul_distrib]

end CubeTilt

/-- Exponential separation for an actual Boolean output map. The only
map-specific hypothesis is a coordinate acceptance gap on every affine cube.
All tilted-law, information, and moment inequalities are proved internally. -/
theorem overlap_bound_of_cube_gap [Nonempty I]
    (t : ℕ) (Q : G → I → Bool) (p δ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 ≤ δ)
    (hvariance : 0 < δ ^ 2 - p * (1-p) / ((2 ^ t : ℕ) : ℝ))
    (hgap : ∀ (z : CubeTilt.Parameters G t) i,
      δ ≤ |(∑ v : Cube.Tuple Bool t, bitValue (CubeTilt.vertexOutput t Q v z i)) /
        ((2 ^ t : ℕ) : ℝ) - p|) :
    CubeTilt.overlap Q (bernoulliProduct p) ≤
      Real.exp (-(amplificationRate (max p (1-p)) ((2 ^ t : ℕ) : ℝ)
        δ (p * (1-p)) * (Fintype.card I : ℝ))) := by
  let M : (I → Bool) → ℝ := bernoulliProduct p
  let μ := CubeTilt.law t Q M
  let Y : CubeTilt.Parameters G t → Cube.Tuple Bool t → I → ℝ :=
    fun z v i => bitValue (CubeTilt.vertexOutput t Q v z i)
  let ω := CubeTilt.overlap Q M
  have hM : ∀ a, 0 < M a := bernoulliProduct_pos p hp hp1
  have hω : 0 < ω := CubeTilt.overlap_pos Q M hM
  have hμ : ∀ z, 0 ≤ μ z := CubeTilt.law_nonneg t Q M (fun a => (hM a).le) hω
  have hμsum : ∑ z, μ z = 1 := CubeTilt.law_sum t Q M (fun a => (hM a).le) hω
  have hm : 0 < max p (1-p) := hp.trans_le (le_max_left _ _)
  have hsingle (v : Cube.Tuple Bool t) :
      finiteKL (CubeTilt.singleLaw t Q M v) M ≤
        (Fintype.card (Cube.Tuple Bool t) : ℝ) * (-Real.log ω) := by
    simpa only [Cube.card_vertices, one_div, Real.log_inv, ω] using
      CubeTilt.single_KL_budget t Q M hM hω v
  have hpair (v w : Cube.Tuple Bool t) (hvw : v ≠ w) :
      finiteKL (CubeTilt.pairedCoordinateLaw t Q M v w)
          (productMass (fun _ (b : Bool × Bool) =>
            bernoulliMass p b.1 * bernoulliMass p b.2)) ≤
        (Fintype.card (Cube.Tuple Bool t) : ℝ) * (-Real.log ω) := by
    rw [CubeTilt.pairedCoordinateLaw_KL]
    simpa only [Cube.card_vertices, one_div, Real.log_inv, ω, M] using
      CubeTilt.pair_KL_budget t Q M hM hω v w hvw
  have hroot {D : ℝ} (hD : D ≤
      (Fintype.card (Cube.Tuple Bool t) : ℝ) * (-Real.log ω)) :
      max p (1-p) * Real.sqrt ((Fintype.card I : ℝ) * D / 2) ≤
      max p (1-p) * Real.sqrt ((Fintype.card I : ℝ) *
        (Fintype.card (Cube.Tuple Bool t) : ℝ) * (-Real.log ω) / 2) := by
    apply mul_le_mul_of_nonneg_left _ hm.le
    apply Real.sqrt_le_sqrt
    have h := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg (Fintype.card I))
    nlinarith
  have hresult := amplification_of_moment_bounds μ hμ hμsum Y p δ
    (p*(1-p)) (max p (1-p)) ω hδ hm hω (CubeTilt.overlap_le_one Q M)
    (by simpa only [Cube.card_vertices] using hvariance)
    (by simpa only [Y, Cube.card_vertices] using hgap)
  suffices H : ω ≤ Real.exp (-(amplificationRate (max p (1-p))
      (Fintype.card (Cube.Tuple Bool t) : ℝ) δ (p*(1-p)) * (Fintype.card I : ℝ))) by
    simpa only [Cube.card_vertices] using H
  apply hresult
  · intro v
    have hR : ∀ a, 0 ≤ CubeTilt.singleLaw t Q M v a :=
      fun a => finiteEventMass_nonneg _ _ hμ
    have htest := product_coordinate_test (CubeTilt.singleLaw t Q M v)
      (fun _ => bernoulliMass p) hR
      (CubeTilt.singleLaw_sum t Q M (fun a => (hM a).le) hω v)
      (fun _ => bernoulliMass_pos p hp hp1) (fun _ => bernoulliMass_sum p)
      (fun _ b => (bitValue b-p)^2) (max p (1-p))
      (fun _ => max p (1-p)/2-p*(1-p)) hm.le
      (fun _ b => bernoulli_diagonal_range p hp.le hp1.le b)
    dsimp only at htest
    simp_rw [bernoulli_variance] at htest
    have ht : |SecondMoment.moment μ Y p v v - (Fintype.card I : ℝ)* (p*(1-p))| ≤
        max p (1-p) * Real.sqrt ((Fintype.card I : ℝ) *
          finiteKL (CubeTilt.singleLaw t Q M v) M / 2) := by
      simpa only [CubeTilt.singleLaw_expectation, bernoulli_variance,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        SecondMoment.moment, SecondMoment.expectation, Y, μ, M, bernoulliProduct,
        pow_two] using htest
    have hh := (le_abs_self _).trans (ht.trans (hroot (hsingle v)))
    linarith
  · intro v w hvw
    have hR : ∀ a, 0 ≤ CubeTilt.pairedCoordinateLaw t Q M v w a :=
      fun a => finiteEventMass_nonneg _ _ hμ
    have hpairsum : (∑ b : Bool × Bool,
        bernoulliMass p b.1 * bernoulliMass p b.2) = 1 := by
      simp [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliMass]
      ring
    have htest := product_coordinate_test (CubeTilt.pairedCoordinateLaw t Q M v w)
      (fun _ (b : Bool × Bool) => bernoulliMass p b.1 * bernoulliMass p b.2) hR
      (CubeTilt.pairedCoordinateLaw_sum t Q M (fun a => (hM a).le) hω v w)
      (fun _ b => mul_pos (bernoulliMass_pos p hp hp1 b.1)
        (bernoulliMass_pos p hp hp1 b.2)) (fun _ => hpairsum)
      (fun _ b => (bitValue b.1-p)*(bitValue b.2-p)) (max p (1-p))
      (fun _ => max p (1-p)/2-p*(1-p)) hm.le
      (fun _ b => bernoulli_pair_range p hp.le hp1.le b)
    dsimp only at htest
    simp_rw [CubeTilt.pairedCoordinateLaw_expectation t Q M v w _
      (fun b : Bool × Bool => (bitValue b.1-p)*(bitValue b.2-p))] at htest
    have ht : |SecondMoment.moment μ Y p v w| ≤
        max p (1-p) * Real.sqrt ((Fintype.card I : ℝ) *
          finiteKL (CubeTilt.pairedCoordinateLaw t Q M v w)
            (productMass (fun _ (b : Bool × Bool) =>
              bernoulliMass p b.1 * bernoulliMass p b.2)) / 2) := by
      simpa only [CubeTilt.pairedCoordinateLaw_expectation, bernoulli_pair_mean,
        sub_zero, SecondMoment.moment, SecondMoment.expectation, Y, μ] using htest
    exact (le_abs_self _).trans (ht.trans (hroot (hpair v w hvw)))

end SamplingLowerBounds
