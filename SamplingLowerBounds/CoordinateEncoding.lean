import SamplingLowerBounds.SourceProjection

/-!
# Explicit coordinate encoding of the padded AND graph

The equivalence acts by permuting individual Boolean coordinates. It is not
an arbitrary bijection of the `2^N` possible output strings.
-/

open Classical

namespace SamplingLowerBounds.FlatGraph

abbrev StructuredOutput (m b u v : ℕ) :=
  ((Fin m → Fin b → Bool) × (Fin u → Bool)) × ((Fin m → Bool) × (Fin v → Bool))

abbrev StructuredIndex (m b u v : ℕ) :=
  ((Fin m × Fin b) ⊕ Fin u) ⊕ (Fin m ⊕ Fin v)

/-- Flatten products of bit vectors by tagging their coordinate indices. -/
def structuredBits (m b u v : ℕ) :
    StructuredOutput m b u v ≃ (StructuredIndex m b u v → Bool) where
  toFun z := Sum.elim (Sum.elim (fun ij => z.1.1 ij.1 ij.2) z.1.2)
    (Sum.elim z.2.1 z.2.2)
  invFun f := ((fun i j => f (.inl (.inl (i,j))), fun j => f (.inl (.inr j))),
    (fun i => f (.inr (.inl i)), fun j => f (.inr (.inr j))))
  left_inv z := rfl
  right_inv f := by
    funext i
    rcases i with (⟨i,j⟩ | j) | (i | j) <;> rfl

/-- Row-major ordering of input blocks followed by unused inputs, active
labels, and zero labels. The maps are explicit finite sums and products. -/
def structuredIndexEquiv (m b u v N : ℕ) (hsize : m*b+u+(m+v) = N) :
    StructuredIndex m b u v ≃ Fin N :=
  ((Equiv.sumCongr
    ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin u))).trans finSumFinEquiv)
    finSumFinEquiv).trans finSumFinEquiv).trans (finCongr hsize)

/-- An explicit permutation of coordinates giving an ordinary `N`-bit vector. -/
def coordinateEncoding (m b u v N : ℕ) (hsize : m*b+u+(m+v) = N) :
    StructuredOutput m b u v ≃ (Fin N → Bool) :=
  (structuredBits m b u v).trans
    (Equiv.arrowCongr (structuredIndexEquiv m b u v N hsize) (Equiv.refl Bool))

/-- Position of an active AND-output coordinate in the flattened vector. -/
def activeIndex (m b u v N : ℕ) (hsize : m*b+u+(m+v) = N) (i : Fin m) : Fin N :=
  structuredIndexEquiv m b u v N hsize (.inr (.inl i))

theorem coordinateEncoding_active (m b u v N : ℕ) (hsize : m*b+u+(m+v) = N)
    (z : StructuredOutput m b u v) (i : Fin m) :
    coordinateEncoding m b u v N hsize z (activeIndex m b u v N hsize i) = z.2.1 i := by
  simp [coordinateEncoding, activeIndex, structuredBits]

theorem coordinateEncoding_symm_active (m b u v N : ℕ) (hsize : m*b+u+(m+v) = N)
    (y : Fin N → Bool) (i : Fin m) :
    ((coordinateEncoding m b u v N hsize).symm y).2.1 i =
      y (activeIndex m b u v N hsize i) := by
  simpa only [Equiv.apply_symm_apply] using
    (coordinateEncoding_active m b u v N hsize
      ((coordinateEncoding m b u v N hsize).symm y) i).symm

theorem uniformMass_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    Information.pushMass (CubeTilt.uniformMass A) e = CubeTilt.uniformMass B := by
  funext b
  have h := pushMass_injective_at (CubeTilt.uniformMass A) e e.injective (e.symm b)
  simpa only [Equiv.apply_symm_apply, CubeTilt.uniformMass, Fintype.card_congr e] using h

theorem massOverlap_equiv {A B : Type*} [Fintype A] [Fintype B]
    (P M : A → ℝ) (e : A ≃ B) :
    massOverlap (Information.pushMass P e) (Information.pushMass M e) = massOverlap P M := by
  apply le_antisymm
  · have h := massOverlap_postprocess (Information.pushMass P e) (Information.pushMass M e) e.symm
    have hP : Information.pushMass (Information.pushMass P e) e.symm = P := by
      funext a
      rw [pushMass_comp]
      simp [Information.pushMass, Function.comp_def]
    have hM : Information.pushMass (Information.pushMass M e) e.symm = M := by
      funext a
      rw [pushMass_comp]
      simp [Information.pushMass, Function.comp_def]
    rwa [hP, hM] at h
  · exact massOverlap_postprocess P M e

end SamplingLowerBounds.FlatGraph
