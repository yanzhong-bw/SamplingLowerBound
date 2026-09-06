import SamplingLowerBounds.ProductTests

open scoped BigOperators
namespace SamplingLowerBounds.Information

def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p
def bitValue (b : Bool) : ℝ := if b then 1 else 0

theorem bernoulliMass_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ b, 0 < bernoulliMass p b := by
  intro b; cases b <;> simp [bernoulliMass] <;> linarith

theorem bernoulliMass_sum (p : ℝ) : ∑ b, bernoulliMass p b = 1 := by
  simp [Fintype.sum_bool, bernoulliMass]

theorem bernoulli_variance (p : ℝ) :
    (∑ b, bernoulliMass p b * (bitValue b-p)^2) = p*(1-p) := by
  simp [Fintype.sum_bool, bernoulliMass, bitValue]; ring

theorem bernoulli_pair_mean (p : ℝ) :
    (∑ b : Bool × Bool, bernoulliMass p b.1 * bernoulliMass p b.2 *
      ((bitValue b.1-p)*(bitValue b.2-p))) = 0 := by
  simp [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliMass, bitValue]; ring

/-- Centering the pair test gives half-range max(p,1-p)/2. -/
theorem bernoulli_pair_range (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b : Bool × Bool) :
    |(bitValue b.1-p)*(bitValue b.2-p) -
      (max p (1-p)/2-p*(1-p))| ≤ max p (1-p)/2 := by
  have h0 : 0 ≤ max p (1-p) := hp.trans (le_max_left _ _)
  have hl := le_max_left p (1-p)
  have hr := le_max_right p (1-p)
  rcases b with ⟨b,c⟩
  cases b <;> cases c <;> simp only [bitValue, Bool.false_eq_true,
    ↓reduceIte] <;> rw [abs_le] <;> constructor <;> nlinarith

theorem bernoulli_diagonal_range (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b : Bool) :
    |(bitValue b-p)^2 - (max p (1-p)/2-p*(1-p))| ≤ max p (1-p)/2 := by
  simpa only [pow_two] using bernoulli_pair_range p hp hp1 (b,b)

end SamplingLowerBounds.Information
