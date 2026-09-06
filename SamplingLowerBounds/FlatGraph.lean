import SamplingLowerBounds.CubeTilt
import SamplingLowerBounds.DataProcessing

/-!
# Flat graph distributions and overlap under projection

All statements concern actual finite mass functions.  In particular the
postprocessing theorem does not assume injectivity, normalization, or positivity.
The graph construction is injective because it retains the entire input.
-/

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.FlatGraph

open Information CubeTilt

noncomputable def massOverlap {A : Type*} [Fintype A] (P M : A → ℝ) : ℝ :=
  ∑ a, min (P a) (M a)

/-- Deterministic postprocessing can only increase overlap. -/
theorem massOverlap_postprocess {A B : Type*} [Fintype A] [Fintype B]
    (P M : A → ℝ) (f : A → B) :
    massOverlap P M ≤ massOverlap (pushMass P f) (pushMass M f) := by
  have h (b : B) : pushMass (fun a => min (P a) (M a)) f b ≤
      min (pushMass P f b) (pushMass M f b) := by
    apply le_min
    · apply Finset.sum_le_sum
      intro a _
      dsimp
      split_ifs
      · exact min_le_left _ _
      · rfl
    · apply Finset.sum_le_sum
      intro a _
      dsimp
      split_ifs
      · exact min_le_right _ _
      · rfl
  calc
    massOverlap P M = ∑ b, pushMass (fun a => min (P a) (M a)) f b :=
      (pushMass_sum _ _).symm
    _ ≤ massOverlap (pushMass P f) (pushMass M f) :=
      Finset.sum_le_sum (fun b _ => h b)

theorem pushMass_comp {A B C : Type*} [Fintype A] [Fintype B]
    (P : A → ℝ) (f : A → B) (g : B → C) (c : C) :
    pushMass (pushMass P f) g c = pushMass P (g ∘ f) c := by
  have h := pushMass_expectation P f (fun b => if g b = c then 1 else 0)
  simpa [pushMass, mul_ite] using h

theorem pushMass_injective_at {A B : Type*} [Fintype A]
    (P : A → ℝ) (f : A → B) (hf : Function.Injective f) (a : A) :
    pushMass P f (f a) = P a := by
  simp only [pushMass, hf.eq_iff]
  simp

theorem pushMass_eq_zero_off_range {A B : Type*} [Fintype A]
    (P : A → ℝ) (f : A → B) (b : B) (hb : b ∉ Set.range f) :
    pushMass P f b = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  exact if_neg (fun ha => hb ⟨a, ha⟩)

/-- Uniform input under an injection is uniform on its image. -/
theorem injective_uniform_mass {A B : Type*} [Fintype A]
    (f : A → B) (hf : Function.Injective f) (b : B) :
    pushMass (uniformMass A) f b =
      if b ∈ Set.range f then 1 / (Fintype.card A : ℝ) else 0 := by
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [pushMass_injective_at _ _ hf]
    simp [uniformMass]
  · rw [pushMass_eq_zero_off_range _ _ _ hb, if_neg hb]

def graphMap {A B : Type*} (F : A → B) (a : A) : A × B := (a, F a)

theorem graphMap_injective {A B : Type*} (F : A → B) :
    Function.Injective (graphMap F) := by
  intro a a' h
  exact congrArg Prod.fst h

noncomputable def graphLaw {A B : Type*} [Fintype A] (F : A → B) :
    A × B → ℝ := pushMass (uniformMass A) (graphMap F)

theorem graphLaw_mass {A B : Type*} [Fintype A] (F : A → B) (a : A) (b : B) :
    graphLaw F (a,b) = if F a = b then 1 / (Fintype.card A : ℝ) else 0 := by
  rw [graphLaw, injective_uniform_mass _ (graphMap_injective F)]
  congr 1
  apply propext
  constructor
  · rintro ⟨a', h⟩
    have h' := congrArg Prod.fst h
    have h'' := congrArg Prod.snd h
    change a' = a at h'
    change F a' = b at h''
    simpa only [h'] using h''
  · intro h
    exact ⟨a, Prod.ext rfl h⟩

theorem graphLaw_nonneg {A B : Type*} [Fintype A] (F : A → B) (z : A × B) :
    0 ≤ graphLaw F z := pushMass_nonneg _ _ (uniformMass_nonneg A) z

theorem graphLaw_sum {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (F : A → B) : ∑ z, graphLaw F z = 1 := by
  rw [graphLaw, pushMass_sum, uniformMass_sum]

theorem graphLaw_support {A B : Type*} [Fintype A] [Nonempty A]
    (F : A → B) : {z | graphLaw F z ≠ 0} = Set.range (graphMap F) := by
  ext z
  rw [Set.mem_setOf_eq, graphLaw, injective_uniform_mass _ (graphMap_injective F)]
  have hn : (1 : ℝ) / Fintype.card A ≠ 0 :=
    (div_pos zero_lt_one (Nat.cast_pos.mpr Fintype.card_pos)).ne'
  by_cases hz : z ∈ Set.range (graphMap F) <;> simp [hz, hn]

theorem graphLaw_support_card {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (F : A → B) : Fintype.card {z // graphLaw F z ≠ 0} = Fintype.card A := by
  have he : {z // graphLaw F z ≠ 0} ≃ A :=
    (Equiv.setCongr (graphLaw_support F)).trans
      (Equiv.ofInjective (graphMap F) (graphMap_injective F)).symm
  exact Fintype.card_congr he

/-- Projection onto labels has exactly the law of the label map. -/
theorem graphLaw_label_projection {A B : Type*} [Fintype A] [Fintype B]
    (F : A → B) (b : B) :
    pushMass (graphLaw F) Prod.snd b = pushMass (uniformMass A) F b := by
  exact pushMass_comp _ _ _ _

/-- The overlap bound for labels transfers to the full flat graph target. -/
theorem overlap_graph_le_label {A B : Type*} [Fintype A] [Fintype B]
    (P : A × B → ℝ) (F : A → B) :
    massOverlap P (graphLaw F) ≤
      massOverlap (pushMass P Prod.snd) (pushMass (uniformMass A) F) := by
  have h := massOverlap_postprocess P (graphLaw F) Prod.snd
  have he : pushMass (graphLaw F) Prod.snd = pushMass (uniformMass A) F :=
    funext (graphLaw_label_projection F)
  rwa [he] at h

theorem overlap_graph_le_processed_labels {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (P : A × B → ℝ) (F : A → B) (g : B → C) :
    massOverlap P (graphLaw F) ≤
      massOverlap (pushMass P (g ∘ Prod.snd)) (pushMass (uniformMass A) (g ∘ F)) := by
  have h := massOverlap_postprocess P (graphLaw F) (g ∘ Prod.snd)
  have he : pushMass (graphLaw F) (g ∘ Prod.snd) =
      pushMass (uniformMass A) (g ∘ F) :=
    funext (fun c => pushMass_comp _ _ _ c)
  rwa [he] at h

theorem uniformMass_fst {A R : Type*} [Fintype A] [Fintype R] [Nonempty R]
    (a : A) : pushMass (uniformMass (A × R)) Prod.fst a = uniformMass A a := by
  simp only [pushMass, Fintype.sum_prod_type, uniformMass]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

theorem uniformMass_unused_seed {A R B : Type*} [Fintype A] [Fintype R]
    [Nonempty R] (F : A → B) (b : B) :
    pushMass (uniformMass (A × R)) (F ∘ Prod.fst) b =
      pushMass (uniformMass A) F b := by
  rw [← pushMass_comp]
  have he : pushMass (uniformMass (A × R)) Prod.fst = uniformMass A :=
    funext uniformMass_fst
  rw [he]

/-- For a `k`-bit seed the graph support has exactly `2^k` elements. -/
theorem boolean_graph_support_card {B : Type*} [Fintype B] (k : ℕ)
    (F : (Fin k → Bool) → B) :
    Fintype.card {z // graphLaw F z ≠ 0} = 2 ^ k := by
  rw [graphLaw_support_card]
  simp

noncomputable def pointMass {A : Type*} (a : A) (b : A) : ℝ :=
  if a = b then 1 else 0

theorem pointMass_overlap {A : Type*} [Fintype A] (a : A) (P : A → ℝ)
    (hP : ∀ b, 0 ≤ P b) (hP1 : P a ≤ 1) :
    massOverlap (pointMass a) P = P a := by
  unfold massOverlap pointMass
  have h (b : A) : min (if a = b then 1 else 0) (P b) =
      if a = b then P a else 0 := by
    by_cases hb : a = b
    · subst b; simp [min_eq_right hP1]
    · simp [hb, min_eq_left (hP b)]
  simp_rw [h]
  simp

/-- A constant sampler already overlaps the graph target by its atom mass. -/
theorem pointMass_graph_overlap {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] (F : A → B) (a : A) :
    massOverlap (pointMass (graphMap F a)) (graphLaw F) =
      1 / (Fintype.card A : ℝ) := by
  have hc : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
  rw [pointMass_overlap _ _ (graphLaw_nonneg F)]
  · exact pushMass_injective_at _ _ (graphMap_injective F) a
  · change pushMass (uniformMass A) (graphMap F) (graphMap F a) ≤ 1
    rw [pushMass_injective_at _ _ (graphMap_injective F)]
    exact (div_le_one (by positivity : (0 : ℝ) < Fintype.card A)).mpr hc

/-- The ambient uniform law has overlap equal to the inverse label-space size. -/
theorem uniform_graph_overlap {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (F : A → B) :
    massOverlap (uniformMass (A × B)) (graphLaw F) =
      1 / (Fintype.card B : ℝ) := by
  have ha : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  have hb : (1 : ℝ) ≤ Fintype.card B := Nat.one_le_cast.mpr Fintype.card_pos
  have hsmall : (1 : ℝ) / ((Fintype.card A : ℝ) * Fintype.card B) ≤
      1 / Fintype.card A := by
    apply one_div_le_one_div_of_le ha
    nlinarith
  unfold massOverlap
  rw [Fintype.sum_prod_type]
  have h (a : A) (b : B) :
      min (uniformMass (A × B) (a,b)) (graphLaw F (a,b)) =
        if F a = b then 1 / ((Fintype.card A : ℝ) * Fintype.card B) else 0 := by
    rw [graphLaw_mass]
    have hu : uniformMass (A × B) (a,b) =
        1 / ((Fintype.card A : ℝ) * Fintype.card B) := by
      simp only [uniformMass, Fintype.card_prod, Nat.cast_mul]
    rw [hu]
    by_cases he : F a = b
    · simp only [if_pos he, min_eq_left hsmall]
    · simp only [if_neg he, min_eq_right (by positivity :
        0 ≤ (1 : ℝ) / ((Fintype.card A : ℝ) * Fintype.card B))]
  simp_rw [h]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

end SamplingLowerBounds.FlatGraph
