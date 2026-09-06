import SamplingLowerBounds.ActualAmplification
import SamplingLowerBounds.BernoulliVariance
import SamplingLowerBounds.BoundedVariance

/-!
# Variance-sensitive amplification for actual output distributions

This gives the cubic rate used for the adjacent-degree hierarchy. Every
information and moment inequality is derived for the actual tilted cube law.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds
open Information

private theorem entropy_test_with_budget {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (M g : I → A → ℝ)
    (hR : ∀ x, 0 ≤ R x) (hRsum : ∑ x, R x = 1)
    (hM : ∀ i a, 0 < M i a) (hMsum : ∀ i, ∑ a, M i a = 1)
    (hmean : ∀ i, ∑ a, M i a * g i a = 0) (hbound : ∀ i a, |g i a| ≤ 1)
    (V B : ℝ) (hV : 0 ≤ V)
    (hvar : (∑ i, ∑ a, M i a * (g i a)^2) ≤ V)
    (hbudget : finiteKL R (productMass M) ≤ B) :
    (∑ x, R x * ∑ i, g i (x i)) ≤ 2 * Real.sqrt (V*B) + B := by
  have hD := finiteKL_nonneg R (productMass M) hR hRsum (productMass_sum M hMsum)
    (fun x => Finset.prod_pos fun i _ => hM i (x i))
  have hroot := Real.sqrt_le_sqrt (mul_le_mul hvar hbudget hD hV)
  have h := finite_entropy_bounded_variance R M g hR hRsum hM hMsum hmean hbound
  linarith

variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I]

/-- The variance-sensitive bound for one actual tilted vertex. -/
theorem cube_diagonal_variance_bound (t : ℕ) (Q : G → I → Bool)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (v : Cube.Tuple Bool t) :
    SecondMoment.moment (CubeTilt.law t Q (bernoulliProduct p))
      (fun z v i => bitValue (CubeTilt.vertexOutput t Q v z i)) p v v ≤
    (Fintype.card I : ℝ) * (p*(1-p)) +
      2 * Real.sqrt (p*(1-p)) * Real.sqrt ((Fintype.card I : ℝ) *
        ((2 ^ t : ℕ) : ℝ) * (-Real.log (CubeTilt.overlap Q (bernoulliProduct p)))) +
      ((2 ^ t : ℕ) : ℝ) * (-Real.log (CubeTilt.overlap Q (bernoulliProduct p))) := by
  let M : (I → Bool) → ℝ := bernoulliProduct p
  let R := CubeTilt.singleLaw t Q M v
  let B := ((2 ^ t : ℕ) : ℝ) * (-Real.log (CubeTilt.overlap Q M))
  have hM : ∀ a, 0 < M a := bernoulliProduct_pos p hp hp1
  have hω := CubeTilt.overlap_pos Q M hM
  have hR : ∀ a, 0 ≤ R a := fun a =>
    finiteEventMass_nonneg _ _ (CubeTilt.law_nonneg t Q M (fun a => (hM a).le) hω)
  have hRsum : ∑ a, R a = 1 := CubeTilt.singleLaw_sum t Q M (fun a => (hM a).le) hω v
  have hv : 0 ≤ p*(1-p) := mul_nonneg hp.le (by linarith)
  have htest := entropy_test_with_budget R (fun _ => bernoulliMass p)
    (fun _ b => (bitValue b-p)^2-p*(1-p)) hR hRsum
    (fun _ => bernoulliMass_pos p hp hp1) (fun _ => bernoulliMass_sum p)
    (fun _ => bernoulli_diagonal_centered_mean p)
    (fun _ => bernoulli_diagonal_centered_abs_le_one p hp.le hp1.le)
    ((Fintype.card I : ℝ)*(p*(1-p))) B (mul_nonneg (Nat.cast_nonneg _) hv)
    (by
      calc
        _ ≤ ∑ _i : I, p*(1-p) := Finset.sum_le_sum fun _ _ =>
          bernoulli_diagonal_variance_le p hp.le hp1.le
        _ = _ := by simp)
    (by simpa only [M, bernoulliProduct, B, one_div, Real.log_inv] using
      CubeTilt.single_KL_budget t Q M hM hω v)
  have hleft : (∑ x, R x * ∑ i, ((bitValue (x i)-p)^2-p*(1-p))) =
      SecondMoment.moment (CubeTilt.law t Q M)
        (fun z v i => bitValue (CubeTilt.vertexOutput t Q v z i)) p v v -
      (Fintype.card I : ℝ)*(p*(1-p)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hRsum, one_mul]
    simp only [R, CubeTilt.singleLaw_expectation, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, SecondMoment.moment,
      SecondMoment.expectation, pow_two]
    ring
  rw [hleft] at htest
  have hsqrt : Real.sqrt ((Fintype.card I : ℝ)*(p*(1-p))*B) =
      Real.sqrt (p*(1-p))*Real.sqrt ((Fintype.card I : ℝ)*B) := by
    rw [← Real.sqrt_mul hv]
    congr 1
    ring
  rw [hsqrt] at htest
  dsimp only [B, M] at htest
  rw [← mul_assoc] at htest
  simpa only [mul_assoc, add_comm, add_left_comm, add_assoc] using (sub_le_iff_le_add.mp htest)

/-- The variance-sensitive bound for two distinct actual tilted vertices. -/
theorem cube_pair_variance_bound (t : ℕ) (Q : G → I → Bool)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (v w : Cube.Tuple Bool t) (hvw : v ≠ w) :
    SecondMoment.moment (CubeTilt.law t Q (bernoulliProduct p))
      (fun z v i => bitValue (CubeTilt.vertexOutput t Q v z i)) p v w ≤
      2 * (p*(1-p)) * Real.sqrt ((Fintype.card I : ℝ) *
        ((2 ^ t : ℕ) : ℝ) * (-Real.log (CubeTilt.overlap Q (bernoulliProduct p)))) +
      ((2 ^ t : ℕ) : ℝ) * (-Real.log (CubeTilt.overlap Q (bernoulliProduct p))) := by
  let M : (I → Bool) → ℝ := bernoulliProduct p
  let R := CubeTilt.pairedCoordinateLaw t Q M v w
  let B := ((2 ^ t : ℕ) : ℝ) * (-Real.log (CubeTilt.overlap Q M))
  have hM : ∀ a, 0 < M a := bernoulliProduct_pos p hp hp1
  have hω := CubeTilt.overlap_pos Q M hM
  have hR : ∀ a, 0 ≤ R a := fun a =>
    finiteEventMass_nonneg _ _ (CubeTilt.law_nonneg t Q M (fun a => (hM a).le) hω)
  have hRsum : ∑ a, R a = 1 :=
    CubeTilt.pairedCoordinateLaw_sum t Q M (fun a => (hM a).le) hω v w
  have hv : 0 ≤ p*(1-p) := mul_nonneg hp.le (by linarith)
  have htest := entropy_test_with_budget R
    (fun _ (b : Bool × Bool) => bernoulliMass p b.1 * bernoulliMass p b.2)
    (fun _ b => (bitValue b.1-p)*(bitValue b.2-p)) hR hRsum
    (fun _ b => mul_pos (bernoulliMass_pos p hp hp1 b.1) (bernoulliMass_pos p hp hp1 b.2))
    (fun _ => by
      simp [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliMass]
      ring)
    (fun _ => bernoulli_pair_mean p)
    (fun _ => bernoulli_pair_abs_le_one p hp.le hp1.le)
    ((Fintype.card I : ℝ)*(p*(1-p))^2) B (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (by simp only [bernoulli_pair_variance, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, le_refl])
    (by
      dsimp only [R]
      rw [CubeTilt.pairedCoordinateLaw_KL]
      simpa only [M, B, one_div, Real.log_inv] using
        CubeTilt.pair_KL_budget t Q M hM hω v w hvw)
  have hleft : (∑ x, R x * ∑ i, ((bitValue (x i).1-p)*(bitValue (x i).2-p))) =
      SecondMoment.moment (CubeTilt.law t Q M)
        (fun z v i => bitValue (CubeTilt.vertexOutput t Q v z i)) p v w := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [R, CubeTilt.pairedCoordinateLaw_expectation t Q M v w _
      (fun b : Bool × Bool => (bitValue b.1-p)*(bitValue b.2-p))]
    rfl
  dsimp only at htest
  rw [hleft] at htest
  have hsqrt : Real.sqrt ((Fintype.card I : ℝ)*(p*(1-p))^2*B) =
      (p*(1-p))*Real.sqrt ((Fintype.card I : ℝ)*B) := by
    rw [show (Fintype.card I : ℝ)*(p*(1-p))^2*B =
      (p*(1-p))^2*((Fintype.card I : ℝ)*B) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hv]
  rw [hsqrt] at htest
  simpa only [B, M, mul_assoc] using htest

/-- Actual exponential overlap bound at the cubic rate `p³/128`.
The structural inputs are a cube acceptance gap of `p` and `2^t p = 2`. -/
theorem cubic_overlap_bound_of_cube_gap [Nonempty I]
    (t : ℕ) (Q : G → I → Bool) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hKp : ((2 ^ t : ℕ) : ℝ)*p = 2)
    (hgap : ∀ (z : CubeTilt.Parameters G t) i,
      p ≤ |(∑ v : Cube.Tuple Bool t, bitValue (CubeTilt.vertexOutput t Q v z i)) /
        ((2 ^ t : ℕ) : ℝ) - p|) :
    CubeTilt.overlap Q (bernoulliProduct p) ≤
      Real.exp (-((Fintype.card I : ℝ)*p^3/128)) := by
  let M : (I → Bool) → ℝ := bernoulliProduct p
  let μ := CubeTilt.law t Q M
  let Y : CubeTilt.Parameters G t → Cube.Tuple Bool t → I → ℝ :=
    fun z v i => bitValue (CubeTilt.vertexOutput t Q v z i)
  let ω := CubeTilt.overlap Q M
  let n : ℝ := Fintype.card I
  let K : ℝ := Fintype.card (Cube.Tuple Bool t)
  let v₀ := p*(1-p)
  let B := K*(-Real.log ω)
  let S := Real.sqrt (n*B)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α := I)
  have hK : 0 < K := by dsimp [K]; exact_mod_cast Fintype.card_pos (α := Cube.Tuple Bool t)
  have hv : 0 ≤ v₀ := mul_nonneg hp.le (by linarith)
  have hvp : v₀ ≤ p := by dsimp [v₀]; nlinarith [sq_nonneg p]
  have hM : ∀ a, 0 < M a := bernoulliProduct_pos p hp hp1
  have hω : 0 < ω := CubeTilt.overlap_pos Q M hM
  have hμ : ∀ z, 0 ≤ μ z := CubeTilt.law_nonneg t Q M (fun a => (hM a).le) hω
  have hμsum : ∑ z, μ z = 1 := CubeTilt.law_sum t Q M (fun a => (hM a).le) hω
  have hdiag (v : Cube.Tuple Bool t) :
      SecondMoment.moment μ Y p v v ≤ n*v₀+2*Real.sqrt v₀*S+B := by
    simpa only [μ, Y, n, v₀, S, B, K, Cube.card_vertices, ω, M, mul_assoc] using
      cube_diagonal_variance_bound t Q p hp hp1 v
  have hoff (v w : Cube.Tuple Bool t) (hvw : v ≠ w) :
      SecondMoment.moment μ Y p v w ≤ 2*v₀*S+B := by
    simpa only [μ, Y, n, v₀, S, B, K, Cube.card_vertices, ω, M, mul_assoc] using
      cube_pair_variance_bound t Q p hp hp1 v w hvw
  have hnonneg : 0 ≤ 2*v₀*S := mul_nonneg (mul_nonneg (by norm_num) hv)
    (Real.sqrt_nonneg _)
  have hlower := SecondMoment.bias_gap_lower_bound μ hμ hμsum Y p p hp.le
    (by simpa only [Y, Cube.card_vertices] using hgap)
  rw [SecondMoment.expected_average_square] at hlower
  have hmatrix := SecondMoment.normalized_matrix_bound
    (fun v w => SecondMoment.moment μ Y p v w)
    (n*v₀+2*Real.sqrt v₀*S) (2*v₀*S+B)
    (fun v => by have h := hdiag v; linarith) hoff
  have hmoment : n*p^2 ≤ n*v₀/K +
      2*(v₀+Real.sqrt v₀/K)*Real.sqrt (n*K*(-Real.log ω)) + K*(-Real.log ω) := by
    have h := hlower.trans hmatrix
    change n*p^2 ≤ (n*v₀+2*Real.sqrt v₀*S)/K+(2*v₀*S+B) at h
    have heq : (n*v₀+2*Real.sqrt v₀*S)/K+(2*v₀*S+B) =
        n*v₀/K + 2*(v₀+Real.sqrt v₀/K)*Real.sqrt (n*K*(-Real.log ω)) +
          K*(-Real.log ω) := by
      dsimp only [S, B]
      simp only [mul_assoc]
      ring
    rwa [heq] at h
  exact varianceSecondMoment_implies_exponentialOverlap hn hK hp hp1.le
    (by simpa only [K, Cube.card_vertices] using hKp) hv hvp hω
    (CubeTilt.overlap_le_one Q M) hmoment

end SamplingLowerBounds
