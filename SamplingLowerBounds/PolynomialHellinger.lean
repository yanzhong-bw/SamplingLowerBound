import SamplingLowerBounds.PolynomialSampling
import SamplingLowerBounds.Hellinger

/-!
# Polynomial tensor repetition and Hellinger affinity

Repeated coordinates are actual polynomials on disjoint blocks of variables.
Their degree and product output law are proved before applying the sampling
bound to arbitrarily many repetitions.
-/

open scoped BigOperators
open Classical
set_option maxHeartbeats 200000

namespace SamplingLowerBounds
open PolynomialModel Information

noncomputable section

/-- Flattening a rectangular family of coordinates preserves every entry. -/
def blockEquiv (m n : ℕ) (α : Type*) :
    (Fin (m*n) → α) ≃ (Fin m → Fin n → α) where
  toFun x i j := x (finProdFinEquiv (i,j))
  invFun x k := x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv x := by
    funext k
    exact congrArg x (finProdFinEquiv.apply_symm_apply k)
  right_inv x := by funext i j; simp

/-- A change of coordinates in both finite seed and output spaces. -/
theorem outputLaw_equiv {G H A B : Type*}
    [Fintype G] [Fintype H] [Fintype A] [Fintype B]
    (e : G ≃ H) (f : A ≃ B) (Q : G → A) (R : H → B)
    (h : ∀ x, f (Q x) = R (e x)) (a : A) :
    CubeTilt.outputLaw Q a = CubeTilt.outputLaw R (f a) := by
  simp only [CubeTilt.outputLaw, CubeTilt.uniform_event]
  apply Fintype.expect_equiv e
  intro x
  have heq : Q x = a ↔ R (e x) = f a := by rw [← h x, f.injective.eq_iff]
  simp only [heq]

/-- Independent seeds give the product of the individual output laws. -/
theorem outputLaw_pi {I G A : Type*}
    [Fintype I] [Fintype G] [Fintype A] [DecidableEq I]
    (Q : I → G → A) (y : I → A) :
    CubeTilt.outputLaw (fun x : I → G => fun i => Q i (x i)) y =
      productMass (fun i => CubeTilt.outputLaw (Q i)) y := by
  simp only [CubeTilt.outputLaw, finiteEventMass, CubeTilt.uniformMass, productMass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i, Q i (x i) = y i
  · have heq : (fun i => Q i (x i)) = y := funext hx
    simp [heq, hx, Fintype.card_fun]
  · have heq : (fun i => Q i (x i)) ≠ y := by
      intro h; exact hx (congrFun h)
    rw [if_neg heq]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Reindexing finite outcomes leaves the affinity unchanged. -/
theorem bhattacharyyaCoeff_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P M : A → ℝ) (R T : B → ℝ)
    (hP : ∀ a, P a = R (e a)) (hM : ∀ a, M a = T (e a)) :
    bhattacharyyaCoeff P M = bhattacharyyaCoeff R T := by
  unfold bhattacharyyaCoeff
  exact Fintype.sum_equiv e _ _ (fun a => by rw [hP a, hM a])

/-- A tensor repetition of a polynomial source, with disjoint seed blocks. -/
def PolynomialModel.Source.tensor {s N d : ℕ} (Q : Source s N d) (m : ℕ) :
    Source (m*s) (m*N) d where
  coordinate k := MvPolynomial.rename
    (fun j => finProdFinEquiv ((finProdFinEquiv.symm k).1,j))
    (Q.coordinate (finProdFinEquiv.symm k).2)
  degree_le k := (MvPolynomial.totalDegree_rename_le _ _).trans
    (Q.degree_le (finProdFinEquiv.symm k).2)

theorem PolynomialModel.Source.tensor_boolEval {s N d : ℕ} (Q : Source s N d) (m : ℕ)
    (x : Fin (m*s) → F₂) :
    blockEquiv m N Bool ((Q.tensor m).boolEval x) =
      fun i => Q.boolEval (blockEquiv m s F₂ x i) := by
  funext i j
  change decide (MvPolynomial.eval x
      (MvPolynomial.rename
        (fun k : Fin s => finProdFinEquiv
          ((finProdFinEquiv.symm (finProdFinEquiv (i,j))).1,k))
        (Q.coordinate (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2)) = 1) =
    decide (MvPolynomial.eval (fun k => x (finProdFinEquiv (i,k))) (Q.coordinate j) = 1)
  rw [finProdFinEquiv.symm_apply_apply, MvPolynomial.eval_rename]
  rfl

theorem PolynomialModel.Source.tensor_outputLaw {s N d : ℕ} (Q : Source s N d) (m : ℕ)
    (y : Fin (m*N) → Bool) :
    CubeTilt.outputLaw (Q.tensor m).boolEval y =
      productMass (fun _ : Fin m => CubeTilt.outputLaw Q.boolEval)
        (blockEquiv m N Bool y) := by
  rw [outputLaw_equiv (blockEquiv m s F₂) (blockEquiv m N Bool)
    (Q.tensor m).boolEval (fun x i => Q.boolEval (x i))
    (fun x => Q.tensor_boolEval m x)]
  exact outputLaw_pi (fun _ : Fin m => Q.boolEval) (blockEquiv m N Bool y)

theorem bernoulliProduct_blocks (m N : ℕ) (p : ℝ) (y : Fin (m*N) → Bool) :
    bernoulliProduct p y =
      productMass (fun _ : Fin m => (bernoulliProduct p : (Fin N → Bool) → ℝ))
        (blockEquiv m N Bool y) := by
  simp only [bernoulliProduct, productMass, blockEquiv, Equiv.coe_fn_mk]
  have h := Fintype.prod_equiv (finProdFinEquiv : Fin m × Fin N ≃ Fin (m*N))
    (fun k => bernoulliMass p (y (finProdFinEquiv k)))
    (fun k => bernoulliMass p (y k)) (fun _ => rfl)
  simpa only [Fintype.prod_prod_type] using h.symm

theorem PolynomialModel.Source.tensor_affinity {s N d : ℕ} (Q : Source s N d) (m : ℕ)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    bhattacharyyaCoeff (CubeTilt.outputLaw (Q.tensor m).boolEval) (bernoulliProduct p) =
      bhattacharyyaCoeff (CubeTilt.outputLaw Q.boolEval) (bernoulliProduct p) ^ m := by
  rw [bhattacharyyaCoeff_equiv (blockEquiv m N Bool)
    (CubeTilt.outputLaw (Q.tensor m).boolEval) (bernoulliProduct p)
    (productMass (fun _ : Fin m => CubeTilt.outputLaw Q.boolEval))
    (productMass (fun _ : Fin m => (bernoulliProduct p : (Fin N → Bool) → ℝ)))
    (fun y => Q.tensor_outputLaw m y) (fun y => bernoulliProduct_blocks m N p y)]
  have hprod := bhattacharyyaCoeff_productMass
    (fun _ : Fin m => CubeTilt.outputLaw Q.boolEval)
    (fun _ : Fin m => (bernoulliProduct p : (Fin N → Bool) → ℝ))
    (fun _ a => CubeTilt.outputLaw_nonneg _ a)
    (fun _ a => (bernoulliProduct_pos p hp hp1 a).le)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

/-- The sharp affinity bound follows by applying the actual polynomial
sampling theorem to all independent repetitions and removing its prefactor. -/
theorem polynomial_oneThird_affinity {s N d : ℕ} (Q : Source s N d)
    (δ : ℝ) (hδ : 0 < δ) (hgap : UniformAcceptanceGap d (1/3) δ) :
    bhattacharyyaCoeff (CubeTilt.outputLaw Q.boolEval) (bernoulliProduct (1/3)) ≤
      Real.exp (-(δ^6 * (N : ℝ)) / 2) := by
  apply tensor_power_remove_prefactor
  intro m hm
  have hmsum : ∑ y : Fin (m*N) → Bool, bernoulliProduct (1/3) y = 1 := by
    convert bernoulliProduct_sum (I := Fin (m*N)) (1/3) using 1
    congr 1
    ext x
    simp
  have hbc := bhattacharyyaCoeff_sq_le_twice_overlap
    (CubeTilt.outputLaw (Q.tensor m).boolEval) (bernoulliProduct (1/3))
    (CubeTilt.outputLaw_nonneg _)
    (fun y => (bernoulliProduct_pos (1/3) (by norm_num) (by norm_num) y).le)
    (CubeTilt.outputLaw_sum _) hmsum
  have hov := polynomial_oneThird_overlap (Q.tensor m) δ hδ hgap
  rw [Q.tensor_affinity m (1/3) (by norm_num) (by norm_num), ← pow_mul] at hbc
  have hb := hbc.trans (mul_le_mul_of_nonneg_left hov (by norm_num : (0:ℝ) ≤ 2))
  simp only [Nat.cast_mul] at hb
  convert hb using 1 <;> congr 1 <;> ring

theorem polynomial_quadratic_affinity {s N : ℕ} (Q : Source s N 2)
    (hgap : PublishedQuadraticGap) :
    bhattacharyyaCoeff (CubeTilt.outputLaw Q.boolEval) (bernoulliProduct (1/3)) ≤
      Real.exp (-((1/(2:ℝ)^26) * (N:ℝ)) / 2) := by
  apply tensor_power_remove_prefactor
  intro m _
  have hmsum : ∑ y : Fin (m*N) → Bool, bernoulliProduct (1/3) y = 1 := by
    convert bernoulliProduct_sum (I := Fin (m*N)) (1/3) using 1
    congr 1
    ext x
    simp
  have hbc := bhattacharyyaCoeff_sq_le_twice_overlap
    (CubeTilt.outputLaw (Q.tensor m).boolEval) (bernoulliProduct (1/3))
    (CubeTilt.outputLaw_nonneg _)
    (fun y => (bernoulliProduct_pos (1/3) (by norm_num) (by norm_num) y).le)
    (CubeTilt.outputLaw_sum _) hmsum
  have hov := polynomial_quadratic_overlap (Q.tensor m) hgap
  rw [Q.tensor_affinity m (1/3) (by norm_num) (by norm_num), ← pow_mul] at hbc
  have hb := hbc.trans (mul_le_mul_of_nonneg_left hov (by norm_num : (0:ℝ) ≤ 2))
  simp only [Nat.cast_mul] at hb
  convert hb using 1 <;> congr 1 <;> ring

end
end SamplingLowerBounds
