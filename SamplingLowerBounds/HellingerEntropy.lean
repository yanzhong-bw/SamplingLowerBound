import SamplingLowerBounds.Hellinger
import SamplingLowerBounds.DataProcessing

/-!
# Hellinger affinity and the two relative-entropy costs

This file proves the finite variational lower bound for a sampler, including
samplers whose image is a proper subset of the output space.
-/

open scoped BigOperators

namespace SamplingLowerBounds.Information

open Classical

/-- A strictly positive input reference dominates the support of every
pushforward input law. No surjectivity of the sampler is needed. -/
theorem pushMass_eq_zero_of_positive_reference_zero
    {A B : Type*} [Fintype A] (R U : A → ℝ) (Q : A → B)
    (hU : ∀ x, 0 < U x) (b : B) (hb : pushMass U Q b = 0) :
    pushMass R Q b = 0 := by
  have hnot : ∀ x, Q x ≠ b := by
    intro x hx
    have hpos := (hU x).trans_le (le_pushMass U Q (fun x => (hU x).le) x)
    rw [hx, hb] at hpos
    exact (lt_irrefl 0) hpos
  simp [pushMass, hnot]

/-- Data processing for arbitrary finite maps, with all zero-mass output
fibers handled explicitly. -/
theorem finiteKL_data_processing_any {A B : Type*} [Fintype A] [Fintype B]
    (R U : A → ℝ) (Q : A → B) (hR : ∀ x, 0 ≤ R x)
    (hRsum : ∑ x, R x = 1) (hU : ∀ x, 0 < U x) :
    finiteKL (pushMass R Q) (pushMass U Q) ≤ finiteKL R U := by
  let T : A → ℝ := fun x => U x * (pushMass R Q (Q x) / pushMass U Q (Q x))
  have hpU (x : A) : 0 < pushMass U Q (Q x) :=
    (hU x).trans_le (le_pushMass U Q (fun x => (hU x).le) x)
  have hpR := pushMass_nonneg R Q hR
  have hT : ∀ x, 0 ≤ T x := fun x =>
    mul_nonneg (hU x).le (div_nonneg (hpR _) (hpU x).le)
  have hTsum : ∑ x, T x = 1 := by
    have he := pushMass_expectation U Q (fun b => pushMass R Q b / pushMass U Q b)
    dsimp [T]
    rw [← he]
    have heach (b : B) : pushMass U Q b * (pushMass R Q b / pushMass U Q b) =
        pushMass R Q b := by
      by_cases hb : pushMass U Q b = 0
      · rw [pushMass_eq_zero_of_positive_reference_zero R U Q hU b hb]
        simp
      · exact mul_div_cancel₀ _ hb
    simp_rw [heach]
    exact (pushMass_sum R Q).trans hRsum
  have hTsupp : ∀ x, R x ≠ 0 → 0 < T x := by
    intro x hx
    have hr : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
    exact mul_pos (hU x) (div_pos (hr.trans_le (le_pushMass R Q hR x)) (hpU x))
  have hpoint (x : A) : R x * Real.log (R x / U x) =
      R x * Real.log (R x / T x) +
        R x * Real.log (pushMass R Q (Q x) / pushMass U Q (Q x)) := by
    by_cases hx : R x = 0
    · simp [hx]
    have hr : 0 < R x := lt_of_le_of_ne (hR x) (Ne.symm hx)
    have hp : 0 < pushMass R Q (Q x) := hr.trans_le (le_pushMass R Q hR x)
    rw [Real.log_div hx (hU x).ne', Real.log_div hx (hTsupp x hx).ne']
    dsimp [T]
    rw [Real.log_mul (hU x).ne' (div_pos hp (hpU x)).ne']
    ring
  have heq : finiteKL R U = finiteKL R T +
      finiteKL (pushMass R Q) (pushMass U Q) := by
    unfold finiteKL
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    congr 1
    exact (pushMass_expectation R Q
      (fun b => Real.log (pushMass R Q b / pushMass U Q b))).symm
  have hn := finiteKL_nonneg_of_support R T hR hT hRsum hTsum hTsupp
  rw [heq]
  linarith

/-- A nonzero probability law has positive affinity with every strictly
positive reference law. -/
theorem bhattacharyyaCoeff_pos_of_reference_pos {A : Type*} [Fintype A]
    (P M : A → ℝ) (hP : ∀ x, 0 ≤ P x) (hPsum : ∑ x, P x = 1)
    (hM : ∀ x, 0 < M x) : 0 < bhattacharyyaCoeff P M := by
  have hex : ∃ x, 0 < P x := by
    by_contra h
    have hz : ∀ x, P x = 0 := by
      intro x
      exact le_antisymm (le_of_not_gt (fun hx => h ⟨x,hx⟩)) (hP x)
    simp [hz] at hPsum
  obtain ⟨x,hx⟩ := hex
  exact (Real.sqrt_pos.2 (mul_pos hx (hM x))).trans_le
    (Finset.single_le_sum (fun a _ => Real.sqrt_nonneg (P a * M a)) (Finset.mem_univ x))

/-- The sum of two relative entropies is bounded below by minus twice the
logarithm of their Hellinger affinity. The first reference may have zeros. -/
theorem finiteKL_add_ge_neg_log_affinity {A : Type*} [Fintype A]
    (R P M : A → ℝ) (hR : ∀ x, 0 ≤ R x) (hRsum : ∑ x, R x = 1)
    (hP : ∀ x, 0 ≤ P x) (hPsum : ∑ x, P x = 1) (hM : ∀ x, 0 < M x)
    (hsupport : ∀ x, R x ≠ 0 → 0 < P x) :
    -2 * Real.log (bhattacharyyaCoeff P M) ≤ finiteKL R P + finiteKL R M := by
  let Z := bhattacharyyaCoeff P M
  have hZ : 0 < Z := bhattacharyyaCoeff_pos_of_reference_pos P M hP hPsum hM
  let H := fun x => Real.sqrt (P x * M x) / Z
  have hH : ∀ x, 0 ≤ H x := fun x => div_nonneg (Real.sqrt_nonneg _) hZ.le
  have hHsum : ∑ x, H x = 1 := by
    dsimp [H]
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hHsupport : ∀ x, R x ≠ 0 → 0 < H x := by
    intro x hx
    exact div_pos (Real.sqrt_pos.2 (mul_pos (hsupport x hx) (hM x))) hZ
  have heach (x : A) : R x * Real.log (R x / P x) + R x * Real.log (R x / M x) =
      2 * (R x * Real.log (R x / H x)) - 2 * (R x * Real.log Z) := by
    by_cases hx : R x = 0
    · simp [hx]
    have hp := hsupport x hx
    rw [Real.log_div hx hp.ne', Real.log_div hx (hM x).ne',
      Real.log_div hx (hHsupport x hx).ne']
    dsimp [H]
    rw [Real.log_div (Real.sqrt_pos.2 (mul_pos hp (hM x))).ne' hZ.ne',
      Real.log_sqrt (mul_nonneg hp.le (hM x).le), Real.log_mul hp.ne' (hM x).ne']
    ring
  have heq : finiteKL R P + finiteKL R M = 2 * finiteKL R H - 2 * Real.log Z := by
    unfold finiteKL
    rw [← Finset.sum_add_distrib]
    simp_rw [heach]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.sum_mul, hRsum, one_mul]
  have hnonneg := finiteKL_nonneg_of_support R H hR hH hRsum hHsum hHsupport
  rw [heq]
  linarith

/-- The manuscript's sampler entropy inequality. The input reference can
be any positive probability law, and in particular the uniform seed law. -/
theorem sampler_entropy_ge_neg_log_affinity {A B : Type*} [Fintype A] [Fintype B]
    (nu U : A → ℝ) (Q : A → B) (M : B → ℝ)
    (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (hU : ∀ x, 0 < U x) (hUsum : ∑ x, U x = 1) (hM : ∀ b, 0 < M b) :
    -2 * Real.log (bhattacharyyaCoeff (pushMass U Q) M) ≤
      finiteKL nu U + finiteKL (pushMass nu Q) M := by
  have hP := pushMass_nonneg U Q (fun x => (hU x).le)
  have hsupport : ∀ b, pushMass nu Q b ≠ 0 → 0 < pushMass U Q b := by
    intro b hb
    apply lt_of_le_of_ne (hP b)
    intro heq
    exact hb (pushMass_eq_zero_of_positive_reference_zero nu U Q hU b heq.symm)
  have hvar := finiteKL_add_ge_neg_log_affinity (pushMass nu Q) (pushMass U Q) M
    (pushMass_nonneg nu Q hnu) ((pushMass_sum nu Q).trans hnusum)
    hP ((pushMass_sum U Q).trans hUsum) hM hsupport
  exact hvar.trans (add_le_add_right (finiteKL_data_processing_any nu U Q hnu hnusum hU) _)

/-- Multiplying by a function of the output commutes with pushforward. -/
theorem pushMass_mul_pull {A B : Type*} [Fintype A]
    (U : A → ℝ) (Q : A → B) (w : B → ℝ) (b : B) :
    pushMass (fun x => U x * w (Q x)) Q b = pushMass U Q b * w b := by
  simp only [pushMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Q x = b
  · simp [hx]
  · simp [hx]

/-- Lifting the normalized geometric mean over the sampler fibers attains
the lower bound. For uniform `U`, this lift is uniform within every fiber. -/
theorem sampler_entropy_minimizer {A B : Type*} [Fintype A] [Fintype B]
    (U : A → ℝ) (Q : A → B) (M : B → ℝ)
    (hU : ∀ x, 0 < U x) (hUsum : ∑ x, U x = 1) (hM : ∀ b, 0 < M b) :
    ∃ nu : A → ℝ, (∀ x, 0 ≤ nu x) ∧ (∑ x, nu x = 1) ∧
      finiteKL nu U + finiteKL (pushMass nu Q) M =
        -2 * Real.log (bhattacharyyaCoeff (pushMass U Q) M) := by
  let P := pushMass U Q
  have hP := pushMass_nonneg U Q (fun x => (hU x).le)
  have hPsum : ∑ b, P b = 1 := (pushMass_sum U Q).trans hUsum
  let Z := bhattacharyyaCoeff P M
  have hZ : 0 < Z := bhattacharyyaCoeff_pos_of_reference_pos P M hP hPsum hM
  let H := fun b => Real.sqrt (P b * M b) / Z
  have hH : ∀ b, 0 ≤ H b := fun b => div_nonneg (Real.sqrt_nonneg _) hZ.le
  have hHsum : ∑ b, H b = 1 := by
    dsimp [H]
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hPimage (x : A) : 0 < P (Q x) :=
    (hU x).trans_le (le_pushMass U Q (fun x => (hU x).le) x)
  have hHimage (x : A) : 0 < H (Q x) :=
    div_pos (Real.sqrt_pos.2 (mul_pos (hPimage x) (hM (Q x)))) hZ
  let nu := fun x => U x * (H (Q x) / P (Q x))
  have hnupos : ∀ x, 0 < nu x := fun x => mul_pos (hU x) (div_pos (hHimage x) (hPimage x))
  have hpush : pushMass nu Q = H := by
    funext b
    rw [show pushMass nu Q b = P b * (H b / P b) by
      exact pushMass_mul_pull U Q (fun b => H b / P b) b]
    by_cases hb : P b = 0
    · simp [H, hb]
    · exact mul_div_cancel₀ _ hb
  have hnusum : ∑ x, nu x = 1 := by
    rw [← pushMass_sum nu Q, hpush]
    exact hHsum
  have hKLlift : finiteKL nu U = finiteKL H P := by
    have hratio (x : A) : nu x / U x = H (Q x) / P (Q x) := by
      dsimp [nu]
      exact mul_div_cancel_left₀ _ (hU x).ne'
    unfold finiteKL
    simp_rw [hratio]
    rw [← pushMass_expectation nu Q (fun b => Real.log (H b / P b)), hpush]
  have heach (b : B) : H b * Real.log (H b / P b) + H b * Real.log (H b / M b) =
      -2 * (H b * Real.log Z) := by
    by_cases hb : P b = 0
    · simp [H, hb]
    have hp : 0 < P b := lt_of_le_of_ne (hP b) (Ne.symm hb)
    have hh : 0 < H b := div_pos (Real.sqrt_pos.2 (mul_pos hp (hM b))) hZ
    rw [Real.log_div hh.ne' hb, Real.log_div hh.ne' (hM b).ne']
    have hlog : Real.log (H b) = (Real.log (P b) + Real.log (M b)) / 2 - Real.log Z := by
      dsimp [H]
      rw [Real.log_div (Real.sqrt_pos.2 (mul_pos hp (hM b))).ne' hZ.ne',
        Real.log_sqrt (mul_nonneg hp.le (hM b).le), Real.log_mul hb (hM b).ne']
    rw [hlog]
    ring
  have hKLH : finiteKL H P + finiteKL H M = -2 * Real.log Z := by
    unfold finiteKL
    rw [← Finset.sum_add_distrib]
    simp_rw [heach]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hHsum, one_mul]
  refine ⟨nu, (fun x => (hnupos x).le), hnusum, ?_⟩
  rw [hKLlift, hpush]
  exact hKLH

/-- The exact minimum identity, expressed as an attained least value. -/
theorem sampler_entropy_isLeast {A B : Type*} [Fintype A] [Fintype B]
    (U : A → ℝ) (Q : A → B) (M : B → ℝ)
    (hU : ∀ x, 0 < U x) (hUsum : ∑ x, U x = 1) (hM : ∀ b, 0 < M b) :
    IsLeast {c : ℝ | ∃ nu : A → ℝ, (∀ x, 0 ≤ nu x) ∧ (∑ x, nu x = 1) ∧
      c = finiteKL nu U + finiteKL (pushMass nu Q) M}
      (-2 * Real.log (bhattacharyyaCoeff (pushMass U Q) M)) := by
  constructor
  · obtain ⟨nu, hnu, hnusum, heq⟩ := sampler_entropy_minimizer U Q M hU hUsum hM
    exact ⟨nu, hnu, hnusum, heq.symm⟩
  · intro c hc
    obtain ⟨nu, hnu, hnusum, rfl⟩ := hc
    exact sampler_entropy_ge_neg_log_affinity nu U Q M hnu hnusum hU hUsum hM

end SamplingLowerBounds.Information
