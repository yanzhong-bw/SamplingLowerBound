import SamplingLowerBounds.PolynomialModel

open scoped BigOperators
open Classical

namespace SamplingLowerBounds.PolynomialModel

noncomputable section

/-- A product gate represented by an actual polynomial over F₂. -/
def blockPolynomial {J σ : Type*} [Fintype J] (f : J → σ) : Polynomial σ :=
  ∏ j, MvPolynomial.X (f j)

theorem blockPolynomial_totalDegree {J σ : Type*} [Fintype J] [Fintype σ]
    (f : J → σ) : (blockPolynomial f).totalDegree = Fintype.card J := by
  change (∏ j, MvPolynomial.monomial (Finsupp.single (f j) 1) (1 : F₂)).totalDegree = _
  rw [← MvPolynomial.monomial_sum_one, MvPolynomial.totalDegree_monomial _ one_ne_zero]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  simp

theorem eval_blockPolynomial {J σ : Type*} [Fintype J]
    (f : J → σ) (x : σ → F₂) :
    MvPolynomial.eval x (blockPolynomial f) = ∏ j, x (f j) := by
  simp [blockPolynomial]

abbrev BlockVariables (I J K : Type*) := (I × J) ⊕ K
abbrev BlockLabels (I L : Type*) := I ⊕ L

/-- The label polynomials for disjoint AND gates, followed by zero labels. -/
def paddedLabelPolynomial {I J K L : Type*} [Fintype J]
    (i : BlockLabels I L) : Polynomial (BlockVariables I J K) :=
  Sum.elim (fun i => blockPolynomial (fun j => Sum.inl (i,j))) (fun _ => 0) i

theorem paddedLabelPolynomial_degree_le {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] (i : BlockLabels I L) :
    (paddedLabelPolynomial (J := J) (K := K) i).totalDegree ≤ Fintype.card J := by
  cases i with
  | inl i => simp only [paddedLabelPolynomial, Sum.elim_inl, blockPolynomial_totalDegree, le_refl]
  | inr i => simp [paddedLabelPolynomial]

theorem paddedLabelPolynomial_active_degree {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] (i : I) :
    (paddedLabelPolynomial (J := J) (K := K) (L := L) (Sum.inl i)).totalDegree =
      Fintype.card J := blockPolynomial_totalDegree _

/-- Retaining all input coordinates gives the polynomial graph sampler. -/
def graphPolynomial {I J K L : Type*} [Fintype J]
    (i : (BlockVariables I J K) ⊕ (BlockLabels I L)) :
    Polynomial (BlockVariables I J K) :=
  Sum.elim MvPolynomial.X paddedLabelPolynomial i

theorem graphPolynomial_degree_le {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Nonempty J]
    (i : (BlockVariables I J K) ⊕ (BlockLabels I L)) :
    (graphPolynomial i).totalDegree ≤ Fintype.card J := by
  cases i with
  | inl i => simpa [graphPolynomial] using Fintype.card_pos (α := J)
  | inr i => exact paddedLabelPolynomial_degree_le i

theorem graphPolynomial_degree_exact {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Nonempty I] :
    ∃ i : (BlockVariables I J K) ⊕ (BlockLabels I L),
      (graphPolynomial i).totalDegree = Fintype.card J := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact ⟨Sum.inr (Sum.inl i), paddedLabelPolynomial_active_degree (L := L) i⟩

/-- Each nonconstant label uses only its own block of variables. -/
theorem paddedLabelPolynomial_locality {I J K L : Type*} [Fintype J]
    (i : I) (x y : BlockVariables I J K → F₂)
    (hxy : ∀ j, x (Sum.inl (i,j)) = y (Sum.inl (i,j))) :
    MvPolynomial.eval x (paddedLabelPolynomial (L := L) (Sum.inl i)) =
      MvPolynomial.eval y (paddedLabelPolynomial (L := L) (Sum.inl i)) := by
  simp only [paddedLabelPolynomial, Sum.elim_inl, eval_blockPolynomial]
  exact Finset.prod_congr rfl (fun j _ => hxy j)

end
end SamplingLowerBounds.PolynomialModel
