import SamplingLowerBounds.BernoulliTests
import SamplingLowerBounds.HellingerEntropy

/-!
# Shannon entropy and total correlation

Exact identities behind the paper's entropy separation corollary, using
natural logarithms and genuine finite input/output laws.
-/

open scoped BigOperators

namespace SamplingLowerBounds.Information

open Classical

noncomputable def finiteEntropy {A : Type*} [Fintype A] (R : A → ℝ) : ℝ :=
  -(∑ x, R x * Real.log (R x))

noncomputable def uniformMass (A : Type*) [Fintype A] (_ : A) : ℝ :=
  1 / (Fintype.card A : ℝ)

theorem uniformMass_pos (A : Type*) [Fintype A] [Nonempty A] (x : A) :
    0 < uniformMass A x := by
  exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem uniformMass_sum (A : Type*) [Fintype A] [Nonempty A] :
    ∑ x, uniformMass A x = 1 := by
  simp [uniformMass, Fintype.card_ne_zero]

/-- Relative entropy from the uniform law is the entropy deficit. -/
theorem finiteKL_uniform_eq_entropy_deficit {A : Type*} [Fintype A] [Nonempty A]
    (R : A → ℝ) (hRsum : ∑ x, R x = 1) :
    finiteKL R (uniformMass A) = Real.log (Fintype.card A : ℝ) - finiteEntropy R := by
  have heach (x : A) : R x * Real.log (R x / uniformMass A x) =
      R x * Real.log (R x) + R x * Real.log (Fintype.card A : ℝ) := by
    rw [mul_log_div _ _ (uniformMass_pos A x).ne']
    simp only [uniformMass, one_div, Real.log_inv]
    ring
  unfold finiteKL finiteEntropy
  simp_rw [heach]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hRsum, one_mul]
  ring

noncomputable def totalCorrelation {I A : Type*} [Fintype I] [Fintype A]
    (R : (I → A) → ℝ) : ℝ := finiteKL R (productMass (marginal R))

theorem finiteKL_bernoulli_eq_binaryKL (R : Bool → ℝ) (hRsum : ∑ b, R b = 1)
    (p : ℝ) : finiteKL R (bernoulliMass p) = binaryKL (R true) p := by
  have hr : R false = 1 - R true := by
    have hm : R true + R false = 1 := by simpa only [Fintype.sum_bool] using hRsum
    linarith
  simp only [finiteKL, Fintype.sum_bool, bernoulliMass, Bool.false_eq_true,
    ↓reduceIte, hr, binaryKL]

/-- Divergence from an independent Bernoulli law is total correlation plus
the sum of the binary marginal divergences. -/
theorem finiteKL_bernoulli_product_decomposition {I : Type*} [Fintype I]
    (R : (I → Bool) → ℝ) (hR : ∀ x, 0 ≤ R x) (hRsum : ∑ x, R x = 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    finiteKL R (productMass (fun _ : I => bernoulliMass p)) =
      totalCorrelation R + ∑ i, binaryKL (marginal R i true) p := by
  rw [finiteKL_product_decomposition R (fun _ => bernoulliMass p)
    hR (fun _ => bernoulliMass_pos p hp hp1)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact finiteKL_bernoulli_eq_binaryKL (marginal R i) (marginal_sum R hRsum i) p

/-- The exact entropy-cost identity in the manuscript, for a finite uniform
seed space. Specializing its cardinality to `2^s` gives `s * log 2`. -/
theorem sampler_entropy_cost_decomposition
    {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    (nu : A → ℝ) (Q : A → (I → Bool))
    (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    finiteKL nu (uniformMass A) +
      finiteKL (pushMass nu Q) (productMass (fun _ : I => bernoulliMass p)) =
    Real.log (Fintype.card A : ℝ) - finiteEntropy nu +
      totalCorrelation (pushMass nu Q) +
        ∑ i, binaryKL (marginal (pushMass nu Q) i true) p := by
  rw [finiteKL_uniform_eq_entropy_deficit nu hnusum,
    finiteKL_bernoulli_product_decomposition (pushMass nu Q)
      (pushMass_nonneg nu Q hnu) ((pushMass_sum nu Q).trans hnusum) p hp hp1]
  ring

/-- For an `s`-bit seed, the uniform entropy is exactly `s log 2`. -/
theorem log_card_boolean_seed (s : ℕ) :
    Real.log (Fintype.card (Fin s → Bool) : ℝ) = (s : ℝ) * Real.log 2 := by
  simp [Fintype.card_fun, Real.log_pow]

/-- The displayed entropy decomposition for Boolean seed spaces. -/
theorem bit_seed_entropy_cost_decomposition {I : Type*} [Fintype I]
    (s : ℕ) (nu : (Fin s → Bool) → ℝ) (Q : (Fin s → Bool) → (I → Bool))
    (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    finiteKL nu (uniformMass (Fin s → Bool)) +
      finiteKL (pushMass nu Q) (productMass (fun _ : I => bernoulliMass p)) =
    (s : ℝ) * Real.log 2 - finiteEntropy nu + totalCorrelation (pushMass nu Q) +
      ∑ i, binaryKL (marginal (pushMass nu Q) i true) p := by
  simpa only [log_card_boolean_seed] using
    sampler_entropy_cost_decomposition nu Q hnu hnusum p hp hp1

/-- Combining the sampler variational inequality with an affinity bound
gives the complete displayed lower bound on the three entropy costs. -/
theorem sampler_entropy_cost_ge_of_affinity_bound
    {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    (nu : A → ℝ) (Q : A → (I → Bool))
    (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (p c : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hbc : bhattacharyyaCoeff (pushMass (uniformMass A) Q)
      (productMass (fun _ : I => bernoulliMass p)) ≤ Real.exp (-c / 2)) :
    c ≤ Real.log (Fintype.card A : ℝ) - finiteEntropy nu +
      totalCorrelation (pushMass nu Q) +
        ∑ i, binaryKL (marginal (pushMass nu Q) i true) p := by
  have hM : ∀ x, 0 < productMass (fun _ : I => bernoulliMass p) x :=
    fun x => Finset.prod_pos fun i _ => bernoulliMass_pos p hp hp1 (x i)
  have hpos := bhattacharyyaCoeff_pos_of_reference_pos
    (pushMass (uniformMass A) Q) (productMass (fun _ : I => bernoulliMass p))
    (pushMass_nonneg (uniformMass A) Q (fun x => (uniformMass_pos A x).le))
    ((pushMass_sum (uniformMass A) Q).trans (uniformMass_sum A)) hM
  have hlog := Real.log_le_log hpos hbc
  rw [Real.log_exp] at hlog
  have hv := sampler_entropy_ge_neg_log_affinity nu (uniformMass A) Q
    (productMass (fun _ : I => bernoulliMass p)) hnu hnusum
    (uniformMass_pos A) (uniformMass_sum A) hM
  rw [sampler_entropy_cost_decomposition nu Q hnu hnusum p hp hp1] at hv
  linarith

end SamplingLowerBounds.Information
