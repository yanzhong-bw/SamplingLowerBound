import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Finite changes of measure and retained-factor marginal bounds

This file proves the algebraic change-of-measure step in the affine-cube
argument.  All laws are finite real-valued mass functions.  Pair independence
is stated as an equality of the *untilted* joint event masses; it is not an
assumption about the tilted law.  No entropy or polynomial results are assumed
or proved here.
-/

open scoped BigOperators

namespace SamplingLowerBounds

variable {Ω V A : Type*}

/-- A product of numbers in `[0,1]` is bounded by any retained factor. -/
theorem product_le_retained_one [DecidableEq V] (s : Finset V) (f : V → ℝ)
    (h0 : ∀ v ∈ s, 0 ≤ f v) (h1 : ∀ v ∈ s, f v ≤ 1)
    (v : V) (hv : v ∈ s) : (∏ j ∈ s, f j) ≤ f v := by
  rw [← Finset.mul_prod_erase s f hv]
  have hrest : (∏ j ∈ s.erase v, f j) ≤ 1 :=
    Finset.prod_le_one
      (fun j hj => h0 j (Finset.mem_of_mem_erase hj))
      (fun j hj => h1 j (Finset.mem_of_mem_erase hj))
  simpa using mul_le_mul_of_nonneg_left hrest (h0 v hv)

/-- Retaining two distinct factors bounds a product of numbers in `[0,1]`. -/
theorem product_le_retained_pair [DecidableEq V] (s : Finset V) (f : V → ℝ)
    (h0 : ∀ v ∈ s, 0 ≤ f v) (h1 : ∀ v ∈ s, f v ≤ 1)
    (v w : V) (hv : v ∈ s) (hw : w ∈ s) (hvw : v ≠ w) :
    (∏ j ∈ s, f j) ≤ f v * f w := by
  rw [← Finset.mul_prod_erase s f hv]
  apply mul_le_mul_of_nonneg_left _ (h0 v hv)
  apply product_le_retained_one (s.erase v) f
    (fun j hj => h0 j (Finset.mem_of_mem_erase hj))
    (fun j hj => h1 j (Finset.mem_of_mem_erase hj)) w
  exact Finset.mem_erase.mpr ⟨Ne.symm hvw, hw⟩

/-- The mass assigned to an event by a finite, possibly unnormalised law. -/
noncomputable def finiteEventMass [Fintype Ω] (μ : Ω → ℝ) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then μ ω else 0

theorem finiteEventMass_nonneg [Fintype Ω] (μ : Ω → ℝ) (E : Ω → Prop)
    (hμ : ∀ ω, 0 ≤ μ ω) : 0 ≤ finiteEventMass μ E := by
  classical
  unfold finiteEventMass
  apply Finset.sum_nonneg
  intro ω _
  by_cases hE : E ω
  · simpa only [if_pos hE] using hμ ω
  · simp only [if_neg hE, le_refl]

/-- The normalising constant for a finite nonnegative tilt. -/
noncomputable def tiltNormalizer [Fintype Ω] (μ W : Ω → ℝ) : ℝ :=
  ∑ ω, μ ω * W ω

/-- A finite law obtained by multiplication by `W` and division by `Z`. -/
noncomputable def finiteTilt (μ W : Ω → ℝ) (Z : ℝ) (ω : Ω) : ℝ :=
  μ ω * W ω / Z

theorem tiltNormalizer_nonneg [Fintype Ω] (μ W : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hW : ∀ ω, 0 ≤ W ω) :
    0 ≤ tiltNormalizer μ W :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ ω) (hW ω))

theorem tiltNormalizer_le_one [Fintype Ω] (μ W : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : (∑ ω, μ ω) = 1)
    (hW : ∀ ω, W ω ≤ 1) : tiltNormalizer μ W ≤ 1 := by
  unfold tiltNormalizer
  calc
    (∑ ω, μ ω * W ω) ≤ ∑ ω, μ ω := by
      apply Finset.sum_le_sum
      intro ω _
      simpa using mul_le_mul_of_nonneg_left (hW ω) (hμ ω)
    _ = 1 := hμsum

theorem finiteTilt_nonneg (μ W : Ω → ℝ) {Z : ℝ}
    (hμ : ∀ ω, 0 ≤ μ ω) (hW : ∀ ω, 0 ≤ W ω) (hZ : 0 < Z) (ω : Ω) :
    0 ≤ finiteTilt μ W Z ω :=
  div_nonneg (mul_nonneg (hμ ω) (hW ω)) hZ.le

/-- The tilt is a probability law when its normalizer is positive. -/
theorem finiteTilt_sum_eq_one [Fintype Ω] (μ W : Ω → ℝ)
    (hZ : 0 < tiltNormalizer μ W) :
    (∑ ω, finiteTilt μ W (tiltNormalizer μ W) ω) = 1 := by
  simp only [finiteTilt, ← Finset.sum_div]
  exact div_self (ne_of_gt hZ)

theorem finiteEventMass_mono_on [Fintype Ω] (μ ν : Ω → ℝ) (E : Ω → Prop)
    (h : ∀ ω, E ω → μ ω ≤ ν ω) : finiteEventMass μ E ≤ finiteEventMass ν E := by
  classical
  unfold finiteEventMass
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω
  · simpa only [if_pos hE] using h ω hE
  · simp only [if_neg hE, le_refl]

theorem finiteEventMass_div [Fintype Ω] (μ : Ω → ℝ) (E : Ω → Prop) (Z : ℝ) :
    finiteEventMass (fun ω => μ ω / Z) E = finiteEventMass μ E / Z := by
  classical
  simp only [finiteEventMass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω <;> simp [hE]

/-- One-coordinate events allow the retained factor to be pulled outside. -/
theorem finiteEventMass_factor [Fintype Ω] (μ : Ω → ℝ) (Y : Ω → A)
    (g : A → ℝ) (a : A) :
    finiteEventMass (fun ω => μ ω * g (Y ω)) (fun ω => Y ω = a) =
      finiteEventMass μ (fun ω => Y ω = a) * g a := by
  classical
  simp only [finiteEventMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : Y ω = a <;> simp [hE]

/-- Two-coordinate events allow both retained factors to be pulled outside. -/
theorem finiteEventMass_pair_factor [Fintype Ω] (μ : Ω → ℝ)
    (Y₁ Y₂ : Ω → A) (g : A → ℝ) (a b : A) :
    finiteEventMass (fun ω => μ ω * (g (Y₁ ω) * g (Y₂ ω)))
        (fun ω => Y₁ ω = a ∧ Y₂ ω = b) =
      finiteEventMass μ (fun ω => Y₁ ω = a ∧ Y₂ ω = b) * (g a * g b) := by
  classical
  simp only [finiteEventMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : Y₁ ω = a ∧ Y₂ ω = b
  · simp [hE, hE.1, hE.2]
  · simp [hE]

/-- Dropping factors of a finite product is valid on every event after tilting. -/
theorem tilted_event_le_retained [Fintype Ω] (μ W H : Ω → ℝ)
    (E : Ω → Prop) {Z : ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hZ : 0 < Z)
    (hWH : ∀ ω, E ω → W ω ≤ H ω) :
    finiteEventMass (finiteTilt μ W Z) E ≤
      finiteEventMass (fun ω => μ ω * H ω) E / Z := by
  rw [← finiteEventMass_div]
  apply finiteEventMass_mono_on
  intro ω hE
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hWH ω hE) (hμ ω)) hZ.le

/-- An untilted marginal identity plus factor retention gives the tilted bound. -/
theorem tilted_single_marginal_le [Fintype Ω] [Fintype V]
    (μ : Ω → ℝ) (Y : V → Ω → A) (g P : A → ℝ)
    {Z : ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hZ : 0 < Z)
    (hg0 : ∀ a, 0 ≤ g a) (hg1 : ∀ a, g a ≤ 1)
    (v : V) (a : A)
    (hLaw : finiteEventMass μ (fun ω => Y v ω = a) = P a) :
    finiteEventMass (finiteTilt μ (fun ω => ∏ j, g (Y j ω)) Z)
        (fun ω => Y v ω = a) ≤ P a * g a / Z := by
  classical
  calc
    _ ≤ finiteEventMass (fun ω => μ ω * g (Y v ω))
          (fun ω => Y v ω = a) / Z := by
      apply tilted_event_le_retained μ _ _ _ hμ hZ
      intro ω _
      exact product_le_retained_one Finset.univ (fun j => g (Y j ω))
        (fun j _ => hg0 _) (fun j _ => hg1 _) v (Finset.mem_univ v)
    _ = P a * g a / Z := by rw [finiteEventMass_factor, hLaw]

/-- Pair independence is used only under the original law, before tilting. -/
theorem tilted_pair_marginal_le [Fintype Ω] [Fintype V]
    (μ : Ω → ℝ) (Y : V → Ω → A) (g P : A → ℝ)
    {Z : ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hZ : 0 < Z)
    (hg0 : ∀ a, 0 ≤ g a) (hg1 : ∀ a, g a ≤ 1)
    (v w : V) (hvw : v ≠ w) (a b : A)
    (hIndep : finiteEventMass μ (fun ω => Y v ω = a ∧ Y w ω = b) = P a * P b) :
    finiteEventMass (finiteTilt μ (fun ω => ∏ j, g (Y j ω)) Z)
        (fun ω => Y v ω = a ∧ Y w ω = b) ≤
      (P a * g a) * (P b * g b) / Z := by
  classical
  calc
    _ ≤ finiteEventMass (fun ω => μ ω * (g (Y v ω) * g (Y w ω)))
          (fun ω => Y v ω = a ∧ Y w ω = b) / Z := by
      apply tilted_event_le_retained μ _ _ _ hμ hZ
      intro ω _
      exact product_le_retained_pair Finset.univ (fun j => g (Y j ω))
        (fun j _ => hg0 _) (fun j _ => hg1 _) v w
        (Finset.mem_univ v) (Finset.mem_univ w) hvw
    _ = (P a * g a) * (P b * g b) / Z := by
      rw [finiteEventMass_pair_factor, hIndep]
      ring

/-- The overlap-induced retention function, including zero-probability outputs. -/
noncomputable def overlapRetention (P M : A → ℝ) (a : A) : ℝ :=
  min (P a) (M a) / P a

theorem overlapRetention_nonneg (P M : A → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a) (a : A) :
    0 ≤ overlapRetention P M a :=
  div_nonneg (le_min (hP a) (hM a)) (hP a)

theorem overlapRetention_le_one (P M : A → ℝ)
    (hP : ∀ a, 0 ≤ P a) (a : A) : overlapRetention P M a ≤ 1 := by
  unfold overlapRetention
  rcases (hP a).eq_or_lt with ha | ha
  · simp [← ha]
  · exact (div_le_one ha).mpr (min_le_left _ _)

theorem mass_mul_overlapRetention (P M : A → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a) (a : A) :
    P a * overlapRetention P M a = min (P a) (M a) := by
  unfold overlapRetention
  rcases (hP a).eq_or_lt with ha | ha
  · simp [← ha, min_eq_left (hM a)]
  · exact mul_div_cancel₀ _ (ne_of_gt ha)

/-- The fibres of a finite map partition the entire mass of a law. -/
theorem finiteEventMass_sum_fibres [Fintype Ω] [Fintype A]
    (μ : Ω → ℝ) (Y : Ω → A) :
    (∑ a, finiteEventMass μ (fun ω => Y ω = a)) = ∑ ω, μ ω := by
  classical
  unfold finiteEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

/-- The joint fibres of two finite maps also partition the original law. -/
theorem finiteEventMass_sum_pair_fibres [Fintype Ω] [Fintype A]
    (μ : Ω → ℝ) (Y₁ Y₂ : Ω → A) :
    (∑ a, ∑ b, finiteEventMass μ (fun ω => Y₁ ω = a ∧ Y₂ ω = b)) =
      ∑ ω, μ ω := by
  simpa only [Fintype.sum_prod_type, Prod.mk.injEq] using
    finiteEventMass_sum_fibres μ (fun ω => (Y₁ ω, Y₂ ω))

/-- A one-vertex retained event has exactly the common mass of `P` and `M`. -/
theorem overlapRetention_weighted_fibre [Fintype Ω]
    (μ : Ω → ℝ) (Y : Ω → A) (P M : A → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a) (a : A)
    (hLaw : finiteEventMass μ (fun ω => Y ω = a) = P a) :
    finiteEventMass (fun ω => μ ω * overlapRetention P M (Y ω))
        (fun ω => Y ω = a) = min (P a) (M a) := by
  rw [finiteEventMass_factor, hLaw, mass_mul_overlapRetention P M hP hM]

/-- The expectation of the overlap retention function is exactly overlap.

This is the equality `E f = omega` at the beginning of the cube proof.  The
hypothesis says precisely that `P` is the pushforward of `mu` under `Y`.
-/
theorem overlapRetention_expectation [Fintype Ω] [Fintype A]
    (μ : Ω → ℝ) (Y : Ω → A) (P M : A → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a)
    (hLaw : ∀ a, finiteEventMass μ (fun ω => Y ω = a) = P a) :
    tiltNormalizer μ (fun ω => overlapRetention P M (Y ω)) =
      ∑ a, min (P a) (M a) := by
  unfold tiltNormalizer
  rw [← finiteEventMass_sum_fibres
    (fun ω => μ ω * overlapRetention P M (Y ω)) Y]
  apply Finset.sum_congr rfl
  intro a _
  exact overlapRetention_weighted_fibre μ Y P M hP hM a (hLaw a)

/-- The one-vertex tilted output law is dominated by the target divided by `Z`. -/
theorem overlap_tilt_single_domination [Fintype Ω] [Fintype V]
    (μ : Ω → ℝ) (Y : V → Ω → A) (P M : A → ℝ)
    {Z : ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hZ : 0 < Z)
    (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a)
    (v : V) (a : A)
    (hLaw : finiteEventMass μ (fun ω => Y v ω = a) = P a) :
    finiteEventMass
        (finiteTilt μ (fun ω => ∏ j, overlapRetention P M (Y j ω)) Z)
        (fun ω => Y v ω = a) ≤ M a / Z := by
  have h := tilted_single_marginal_le μ Y (overlapRetention P M) P hμ hZ
    (overlapRetention_nonneg P M hP hM) (overlapRetention_le_one P M hP) v a hLaw
  rw [mass_mul_overlapRetention P M hP hM] at h
  exact h.trans (div_le_div_of_nonneg_right (min_le_right _ _) hZ.le)

/-- The pair-vertex tilted output law is dominated by `M × M / Z`.

This is the domination bound preceding equation (pair KL bound) in the paper.
The hypothesis `hIndep` concerns the untilted pair.  No independence of the
tilted outputs is required or asserted.
-/
theorem overlap_tilt_pair_domination [Fintype Ω] [Fintype V]
    (μ : Ω → ℝ) (Y : V → Ω → A) (P M : A → ℝ)
    {Z : ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hZ : 0 < Z)
    (hP : ∀ a, 0 ≤ P a) (hM : ∀ a, 0 ≤ M a)
    (v w : V) (hvw : v ≠ w) (a b : A)
    (hIndep : finiteEventMass μ (fun ω => Y v ω = a ∧ Y w ω = b) = P a * P b) :
    finiteEventMass
        (finiteTilt μ (fun ω => ∏ j, overlapRetention P M (Y j ω)) Z)
        (fun ω => Y v ω = a ∧ Y w ω = b) ≤ M a * M b / Z := by
  have h := tilted_pair_marginal_le μ Y (overlapRetention P M) P hμ hZ
    (overlapRetention_nonneg P M hP hM) (overlapRetention_le_one P M hP)
    v w hvw a b hIndep
  rw [mass_mul_overlapRetention P M hP hM,
    mass_mul_overlapRetention P M hP hM] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ hZ.le
  exact mul_le_mul (min_le_right _ _) (min_le_right _ _)
    (le_min (hP b) (hM b)) (hM a)

end SamplingLowerBounds
