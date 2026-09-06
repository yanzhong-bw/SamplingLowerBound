import SamplingLowerBounds.PolynomialModel

/-!
# Bounded functional rank reduces to bounded polynomial degree

Every Boolean function is represented explicitly by its truth-table
interpolation polynomial. Substituting `r` polynomials of degree at most `d`
therefore produces an actual polynomial of degree at most `d*r`.
-/

open scoped BigOperators

namespace SamplingLowerBounds.PolynomialModel

open Classical
noncomputable section

/-- Substituting degree-at-most-`d` polynomials multiplies the total degree
by at most `d`. This holds over every commutative semiring. -/
theorem totalDegree_substitution {σ τ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (f : σ → MvPolynomial τ R) (d : ℕ)
    (hf : ∀ i, (f i).totalDegree ≤ d) :
    (MvPolynomial.eval₂ MvPolynomial.C f p).totalDegree ≤ p.totalDegree * d := by
  conv_lhs => rw [p.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  calc
    _ ≤ (MvPolynomial.C (MvPolynomial.coeff m p)).totalDegree +
        (m.prod fun i e => f i ^ e).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (m.prod fun i e => f i ^ e).totalDegree := by simp
    _ ≤ ∑ i ∈ m.support, (f i ^ m i).totalDegree := MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ i ∈ m.support, m i * d := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left (m i) (hf i))
    _ = (∑ i ∈ m.support, m i) * d := (Finset.sum_mul ..).symm
    _ ≤ p.totalDegree * d := Nat.mul_le_mul_right d (MvPolynomial.le_totalDegree hm)

/-- The linear polynomial equal to one exactly when coordinate `j` equals
the prescribed bit `a`. The second branch is the polynomial `1-X_j`. -/
def bitIndicator {ι : Type*} (j : ι) (a : F₂) : Polynomial ι :=
  if a = 1 then MvPolynomial.X j
  else MvPolynomial.C 1 + MvPolynomial.C (-1) * MvPolynomial.X j

theorem bitIndicator_totalDegree {ι : Type*} (j : ι) (a : F₂) :
    (bitIndicator j a).totalDegree ≤ 1 := by
  unfold bitIndicator
  split_ifs
  · simp
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem eval_bitIndicator {ι : Type*} (x : ι → F₂) (j : ι) (a : F₂) :
    MvPolynomial.eval x (bitIndicator j a) = if x j = a then 1 else 0 := by
  simp only [bitIndicator]
  generalize heq : x j = b
  fin_cases a <;> fin_cases b <;> norm_num [heq]

/-- Truth-table interpolation on the Boolean cube. The coefficient of each
point indicator is the value of the arbitrary function at that point. -/
def truthTablePolynomial {ι : Type*} [Fintype ι]
    (Gamma : (ι → F₂) → F₂) : Polynomial ι :=
  ∑ a : ι → F₂, MvPolynomial.C (Gamma a) * ∏ j, bitIndicator j (a j)

theorem eval_truthTablePolynomial {ι : Type*} [Fintype ι]
    (Gamma : (ι → F₂) → F₂) (x : ι → F₂) :
    MvPolynomial.eval x (truthTablePolynomial Gamma) = Gamma x := by
  simp only [truthTablePolynomial, map_sum, map_mul, MvPolynomial.eval_C, map_prod,
    eval_bitIndicator, Fintype.prod_boole]
  have heq (a : ι → F₂) : (∀ j, x j = a j) ↔ x = a := funext_iff.symm
  simp_rw [heq]
  simp

theorem truthTablePolynomial_totalDegree {ι : Type*} [Fintype ι]
    (Gamma : (ι → F₂) → F₂) :
    (truthTablePolynomial Gamma).totalDegree ≤ Fintype.card ι := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  calc
    _ ≤ (MvPolynomial.C (Gamma a)).totalDegree +
      (∏ j, bitIndicator j (a j)).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (∏ j, bitIndicator j (a j)).totalDegree := by simp
    _ ≤ ∑ j, (bitIndicator j (a j)).totalDegree := MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ _j : ι, 1 := Finset.sum_le_sum fun j _ => bitIndicator_totalDegree j (a j)
    _ = Fintype.card ι := by simp

/-- An explicit polynomial representing the composition of an arbitrary
Boolean function with a tuple of polynomials. -/
def functionalComposition {σ ι : Type*} [Fintype ι]
    (Gamma : (ι → F₂) → F₂) (g : ι → Polynomial σ) : Polynomial σ :=
  MvPolynomial.eval₂ MvPolynomial.C g (truthTablePolynomial Gamma)

theorem eval_functionalComposition {σ ι : Type*} [Fintype ι]
    (Gamma : (ι → F₂) → F₂) (g : ι → Polynomial σ) (x : σ → F₂) :
    MvPolynomial.eval x (functionalComposition Gamma g) =
      Gamma (fun j => MvPolynomial.eval x (g j)) := by
  unfold functionalComposition
  rw [← MvPolynomial.eval_assoc]
  exact eval_truthTablePolynomial Gamma _

theorem functionalComposition_totalDegree {σ ι : Type*} [Fintype ι]
    (Gamma : (ι → F₂) → F₂) (g : ι → Polynomial σ) (d : ℕ)
    (hg : ∀ j, (g j).totalDegree ≤ d) :
    (functionalComposition Gamma g).totalDegree ≤ d * Fintype.card ι := by
  calc
    _ ≤ (truthTablePolynomial Gamma).totalDegree * d :=
      totalDegree_substitution _ g d hg
    _ ≤ Fintype.card ι * d := Nat.mul_le_mul_right d (truthTablePolynomial_totalDegree Gamma)
    _ = d * Fintype.card ι := Nat.mul_comm _ _

/-- Arbitrary functional dependence on `r` degree-`d` polynomials admits a
degree-`d*r` representative; the polynomial representation is constructed. -/
theorem bounded_functional_rank_polynomial {σ : Type*} (r d : ℕ)
    (Gamma : (Fin r → F₂) → F₂) (g : Fin r → Polynomial σ)
    (hg : ∀ j, (g j).totalDegree ≤ d) :
    ∃ p : Polynomial σ, p.totalDegree ≤ d * r ∧
      ∀ x, MvPolynomial.eval x p = Gamma (fun j => MvPolynomial.eval x (g j)) := by
  exact ⟨functionalComposition Gamma g,
    by simpa using functionalComposition_totalDegree Gamma g d hg,
    eval_functionalComposition Gamma g⟩

/-- A source whose individual coordinates have bounded functional rank.
The inner polynomials and the arbitrary combining function may differ
between output coordinates. -/
structure FunctionalSource (s N d r : ℕ) where
  inner : Fin N → Fin r → Polynomial (Fin s)
  combine : Fin N → (Fin r → F₂) → F₂
  degree_le : ∀ i j, (inner i j).totalDegree ≤ d

def FunctionalSource.eval {s N d r : ℕ} (Q : FunctionalSource s N d r)
    (x : Fin s → F₂) : Fin N → F₂ :=
  fun i => Q.combine i (fun j => MvPolynomial.eval x (Q.inner i j))

/-- Compiling a functional source produces an actual bounded-degree
polynomial source with the same seed space and output distribution. -/
def FunctionalSource.toPolynomialSource {s N d r : ℕ} (Q : FunctionalSource s N d r) :
    Source s N (d * r) where
  coordinate i := functionalComposition (Q.combine i) (Q.inner i)
  degree_le i := by
    simpa using functionalComposition_totalDegree (Q.combine i) (Q.inner i) d (Q.degree_le i)

theorem FunctionalSource.eval_toPolynomialSource {s N d r : ℕ}
    (Q : FunctionalSource s N d r) (x : Fin s → F₂) :
    Q.toPolynomialSource.eval x = Q.eval x := by
  funext i
  exact eval_functionalComposition (Q.combine i) (Q.inner i) x

end
end SamplingLowerBounds.PolynomialModel
