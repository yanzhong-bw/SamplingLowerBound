import SamplingLowerBounds.Tensorization
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Entropy and bounded variance

Finite variational relative-entropy and bounded-coordinate exponential-moment
estimates, for the variance-sensitive amplification argument.
-/

open scoped BigOperators

namespace SamplingLowerBounds.Information

open Classical

/-- The finite exponential variational inequality, obtained by tilting the
reference distribution and applying Gibbs' inequality. -/
theorem finiteKL_variational {A : Type*} [Fintype A]
    (R M f : A → ℝ) (hR : ∀ x, 0 ≤ R x) (hM : ∀ x, 0 < M x)
    (hRsum : ∑ x, R x = 1) (hMsum : ∑ x, M x = 1) :
    (∑ x, R x * f x) ≤ finiteKL R M + Real.log (∑ x, M x * Real.exp (f x)) := by
  let Z := ∑ x, M x * Real.exp (f x)
  have hn : Nonempty A := by
    by_contra h
    haveI : IsEmpty A := not_nonempty_iff.mp h
    simp at hMsum
  letI := hn
  have hZ : 0 < Z := Finset.sum_pos (fun x _ => mul_pos (hM x) (Real.exp_pos _))
    Finset.univ_nonempty
  let T := fun x => M x * Real.exp (f x) / Z
  have hT : ∀ x, 0 < T x := fun x => div_pos (mul_pos (hM x) (Real.exp_pos _)) hZ
  have hTsum : ∑ x, T x = 1 := by
    dsimp [T]
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hkl := finiteKL_nonneg R T hR hRsum hTsum hT
  have heq : finiteKL R T = finiteKL R M - (∑ x, R x * f x) + Real.log Z := by
    have heach (x : A) : R x * Real.log (R x / T x) =
        R x * Real.log (R x / M x) - R x * f x + R x * Real.log Z := by
      by_cases hx : R x = 0
      · simp [hx]
      rw [Real.log_div hx (hT x).ne', Real.log_div hx (hM x).ne']
      dsimp [T]
      rw [Real.log_div (mul_ne_zero (hM x).ne' (Real.exp_ne_zero _)) hZ.ne',
        Real.log_mul (hM x).ne' (Real.exp_ne_zero _), Real.log_exp]
      ring
    unfold finiteKL
    simp_rw [heach]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hRsum, one_mul]
  rw [heq] at hkl
  exact sub_le_iff_le_add.mp (by linarith)

/-- A quadratic upper bound for the exponential on the unit interval. -/
theorem exp_le_one_add_add_sq {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have h := Complex.norm_exp_sub_one_sub_id_le (x := (u : ℂ)) (by simpa using hu)
  have hh : |Real.exp u - 1 - u| ≤ u ^ 2 := by
    simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  linarith [(abs_le.mp hh).2]

/-- Centering removes the linear term in the exponential moment. -/
theorem finite_mgf_le_exp_variance {A : Type*} [Fintype A]
    (M g : A → ℝ) (hM : ∀ x, 0 ≤ M x) (hMsum : ∑ x, M x = 1)
    (hmean : ∑ x, M x * g x = 0) (hbound : ∀ x, |g x| ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (∑ x, M x * Real.exp (lam * g x)) ≤
      Real.exp (lam ^ 2 * ∑ x, M x * (g x)^2) := by
  have hp (x : A) : Real.exp (lam * g x) ≤ 1 + lam * g x + (lam * g x)^2 := by
    apply exp_le_one_add_add_sq
    rw [abs_mul, abs_of_nonneg hlam]
    exact (mul_le_mul_of_nonneg_left (hbound x) hlam).trans (by simpa using hlam1)
  calc
    (∑ x, M x * Real.exp (lam * g x)) ≤
        ∑ x, M x * (1 + lam * g x + (lam * g x)^2) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hp x) (hM x)
    _ = 1 + lam ^ 2 * ∑ x, M x * (g x)^2 := by
      simp_rw [show ∀ x, M x * (1 + lam * g x + (lam * g x)^2) =
        M x + lam * (M x * g x) + lam^2 * (M x * (g x)^2) by intro x; ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hMsum, hmean]
      ring
    _ ≤ _ := by linarith [Real.add_one_le_exp (lam ^ 2 * ∑ x, M x * (g x)^2)]

/-- The product law factors the exponential moment of the sum of the
coordinate functions. -/
theorem product_mgf_eq {I A : Type*} [Fintype I] [Fintype A]
    (M g : I → A → ℝ) (lam : ℝ) :
    (∑ x, productMass M x * Real.exp (lam * ∑ i, g i (x i))) =
      ∏ i, ∑ a, M i a * Real.exp (lam * g i a) := by
  simp_rw [Finset.mul_sum, Real.exp_sum, productMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => M i a * Real.exp (lam * g i a))).symm

/-- Bounded, centered independent coordinates have a variance-sensitive
exponential moment bound. -/
theorem product_mgf_le_exp_variance {I A : Type*} [Fintype I] [Fintype A]
    (M g : I → A → ℝ) (hM : ∀ i a, 0 ≤ M i a)
    (hMsum : ∀ i, ∑ a, M i a = 1)
    (hmean : ∀ i, ∑ a, M i a * g i a = 0) (hbound : ∀ i a, |g i a| ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (∑ x, productMass M x * Real.exp (lam * ∑ i, g i (x i))) ≤
      Real.exp (lam ^ 2 * ∑ i, ∑ a, M i a * (g i a)^2) := by
  rw [product_mgf_eq]
  calc
    (∏ i, ∑ a, M i a * Real.exp (lam * g i a)) ≤
        ∏ i, Real.exp (lam ^ 2 * ∑ a, M i a * (g i a)^2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg fun a _ => mul_nonneg (hM i a) (Real.exp_nonneg _)
      · intro i _
        exact finite_mgf_le_exp_variance (M i) (g i) (hM i) (hMsum i)
          (hmean i) (hbound i) lam hlam hlam1
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

/-- The entropy variational inequality applied to the product moment bound. -/
theorem finite_entropy_variance_parametric {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (M g : I → A → ℝ)
    (hR : ∀ x, 0 ≤ R x) (hRsum : ∑ x, R x = 1)
    (hM : ∀ i a, 0 < M i a) (hMsum : ∀ i, ∑ a, M i a = 1)
    (hmean : ∀ i, ∑ a, M i a * g i a = 0) (hbound : ∀ i a, |g i a| ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam * (∑ x, R x * ∑ i, g i (x i)) ≤ finiteKL R (productMass M) +
      lam ^ 2 * ∑ i, ∑ a, M i a * (g i a)^2 := by
  have hpM : ∀ x, 0 < productMass M x := fun x =>
    Finset.prod_pos fun i _ => hM i (x i)
  have hmgf := product_mgf_le_exp_variance M g (fun i a => (hM i a).le)
    hMsum hmean hbound lam hlam hlam1
  have hn : Nonempty (I → A) := by
    by_contra h
    haveI : IsEmpty (I → A) := not_nonempty_iff.mp h
    simp at hRsum
  letI := hn
  have hZ : 0 < ∑ x, productMass M x * Real.exp (lam * ∑ i, g i (x i)) :=
    Finset.sum_pos (fun x _ => mul_pos (hpM x) (Real.exp_pos _)) Finset.univ_nonempty
  have hlog := Real.log_le_log hZ hmgf
  rw [Real.log_exp] at hlog
  have hv := finiteKL_variational R (productMass M) (fun x => lam * ∑ i, g i (x i))
    hR hpM hRsum (productMass_sum M hMsum)
  have hs : (∑ x, R x * (lam * ∑ i, g i (x i))) =
      lam * (∑ x, R x * ∑ i, g i (x i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hs] at hv
  exact hv.trans (add_le_add_left hlog _)

/-- Optimization of the entropy moment inequality, including zero entropy
and zero variance. -/
theorem entropy_variance_optimization (E D V : ℝ) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (h : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → lam * E ≤ D + lam ^ 2 * V) :
    E ≤ 2 * Real.sqrt (V * D) + D := by
  by_cases hD0 : D = 0
  · subst D
    simp only [mul_zero, Real.sqrt_zero, zero_add] at *
    by_contra hE
    have hEp : 0 < E := lt_of_not_ge hE
    have hc : 0 < V + E := add_pos_of_nonneg_of_pos hV hEp
    have hl : 0 < E / (V + E) := div_pos hEp hc
    have hl1 : E / (V + E) ≤ 1 := (div_le_one hc).mpr (by linarith)
    have huse := h (E / (V + E)) hl hl1
    have hsmall : E / (V + E) * V < E := by
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ hc).mpr (by nlinarith [sq_pos_of_pos hEp])
    nlinarith [mul_pos hl (sub_pos.mpr hsmall)]
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    let a := Real.sqrt D
    let b := Real.sqrt V
    have ha : 0 < a := Real.sqrt_pos.2 hDp
    have hb : 0 ≤ b := Real.sqrt_nonneg V
    have hc : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
    have ha2 : a ^ 2 = D := Real.sq_sqrt hD
    have hb2 : b ^ 2 = V := Real.sq_sqrt hV
    have hl : 0 < a / (a + b) := div_pos ha hc
    have hl1 : a / (a + b) ≤ 1 := (div_le_one hc).mpr (by linarith)
    have hroot : Real.sqrt (V * D) = b * a := Real.sqrt_mul hV D
    have hbound : D + (a / (a + b))^2 * V ≤
        (a / (a + b)) * (2 * Real.sqrt (V * D) + D) := by
      rw [hroot, ← ha2, ← hb2]
      apply (mul_le_mul_right (sq_pos_of_pos hc)).mp
      field_simp [hc.ne']
      rw [show a * (2 * (b * a) + a ^ 2) * (a + b) ^ 2 / (a + b) =
        a * (2 * (b * a) + a ^ 2) * (a + b) by field_simp [hc.ne']; ring]
      nlinarith [mul_nonneg (pow_nonneg ha.le 3) hb]
    exact (mul_le_mul_left hl).mp ((h _ hl hl1).trans hbound)

/-- Entropy and bounded variance for arbitrary finite laws and a strictly
positive product reference. This is the full finite version of the paper's
entropy-and-bounded-variance lemma, with the moment bounds proved above. -/
theorem finite_entropy_bounded_variance {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) (M g : I → A → ℝ)
    (hR : ∀ x, 0 ≤ R x) (hRsum : ∑ x, R x = 1)
    (hM : ∀ i a, 0 < M i a) (hMsum : ∀ i, ∑ a, M i a = 1)
    (hmean : ∀ i, ∑ a, M i a * g i a = 0) (hbound : ∀ i a, |g i a| ≤ 1) :
    (∑ x, R x * ∑ i, g i (x i)) ≤
      2 * Real.sqrt ((∑ i, ∑ a, M i a * (g i a)^2) * finiteKL R (productMass M)) +
        finiteKL R (productMass M) := by
  apply entropy_variance_optimization
  · exact finiteKL_nonneg R (productMass M) hR hRsum (productMass_sum M hMsum)
      (fun x => Finset.prod_pos fun i _ => hM i (x i))
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
      mul_nonneg (hM i a).le (sq_nonneg _)
  · intro lam hlam hlam1
    exact finite_entropy_variance_parametric R M g hR hRsum hM hMsum
      hmean hbound lam hlam.le hlam1

end SamplingLowerBounds.Information
