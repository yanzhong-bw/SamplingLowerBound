import SamplingLowerBounds.AndPolynomialBridge

/-!
# A costed executable hierarchy sampler

The cost model counts binary AND gates, equivalently multiplications of bits
in F₂. Input reads, copying, indexing, and writing constant zero coordinates
carry zero field-operation cost. The evaluator accumulates one unit at each
actual gate; the final product count is proved by structural induction.
-/

open Classical

namespace SamplingLowerBounds.PolynomialModel

open FlatGraph

/-- A gate evaluation together with its accumulated field-multiplication count. -/
abbrev CostedBit := Bool × ℕ

def inputBit (b : Bool) : CostedBit := (b, 0)

def multiplyBits (a b : CostedBit) : CostedBit :=
  (a.1 && b.1, a.2+b.2+1)

/-- A counted AND gate is exactly one multiplication of the corresponding F₂ bits. -/
theorem multiplyBits_value (a b : CostedBit) :
    boolEquivF₂ (multiplyBits a b).1 = boolEquivF₂ a.1 * boolEquivF₂ b.1 := by
  rcases a with ⟨a, ca⟩
  rcases b with ⟨b, cb⟩
  cases a <;> cases b <;> simp [multiplyBits, boolEquivF₂]

def costedAnd : (d : ℕ) → (Fin (d+1) → Bool) → CostedBit
  | 0, x => inputBit (x 0)
  | d+1, x => multiplyBits (inputBit (x 0)) (costedAnd d (fun i => x i.succ))

theorem costedAnd_true (d : ℕ) (x : Fin (d+1) → Bool) :
    (costedAnd d x).1 = true ↔ ∀ i, x i = true := by
  induction d with
  | zero => simp [costedAnd, inputBit, Fin.forall_fin_succ]
  | succ d ih =>
    simp only [costedAnd, multiplyBits, inputBit, Bool.and_eq_true, ih,
      Fin.forall_fin_succ]

theorem costedAnd_value (d : ℕ) (x : Fin (d+1) → Bool) :
    (costedAnd d x).1 = blockAND x := by
  have h : (costedAnd d x).1 = true ↔ blockAND x = true := by
    simpa only [blockAND, decide_eq_true_eq] using costedAnd_true d x
  cases ha : (costedAnd d x).1 <;> cases hb : blockAND x <;> simp_all

theorem costedAnd_cost (d : ℕ) (x : Fin (d+1) → Bool) :
    (costedAnd d x).2 = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [costedAnd, multiplyBits, inputBit, ih]

/-- Evaluate the blocks sequentially, accumulating the gate counts actually returned. -/
def costedBlocks : (m d : ℕ) → (Fin m → Fin (d+1) → Bool) → (Fin m → Bool) × ℕ
  | 0, _, _ => (Fin.elim0, 0)
  | m+1, d, x =>
      let head := costedAnd d (x 0)
      let tail := costedBlocks m d (fun i => x i.succ)
      (Fin.cons head.1 tail.1, head.2+tail.2)

theorem costedBlocks_value (m d : ℕ) (x : Fin m → Fin (d+1) → Bool) :
    (costedBlocks m d x).1 = disjointAND x := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
    simp only [costedBlocks, costedAnd_value, ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem costedBlocks_cost (m d : ℕ) (x : Fin m → Fin (d+1) → Bool) :
    (costedBlocks m d x).2 = m*d := by
  induction m with
  | zero => simp [costedBlocks]
  | succ m ih =>
    simp only [costedBlocks, costedAnd_cost, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- Keep unused seed bits and append zero labels without extra multiplications. -/
def costedPaddedAND (m d u v : ℕ)
    (x : (Fin m → Fin (d+1) → Bool) × (Fin u → Bool)) :
    ((Fin m → Bool) × (Fin v → Bool)) × ℕ :=
  let r := costedBlocks m d x.1
  ((r.1, fun _ => false), r.2)

theorem costedPaddedAND_value (m d u v : ℕ)
    (x : (Fin m → Fin (d+1) → Bool) × (Fin u → Bool)) :
    (costedPaddedAND m d u v x).1 = paddedAND x := by
  simp only [costedPaddedAND, costedBlocks_value, paddedAND]

theorem costedPaddedAND_cost (m d u v : ℕ)
    (x : (Fin m → Fin (d+1) → Bool) × (Fin u → Bool)) :
    (costedPaddedAND m d u v x).2 = m*d := costedBlocks_cost m d x.1

/-- Full executable canonical sampler with a structurally accumulated gate count. -/
def costedCanonicalSampler (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (x : Fin k → Bool) :
    (Fin N → Bool) × ℕ :=
  let seed := splitSeed m (d+1) u k hk x
  let r := costedPaddedAND m d u v seed
  (coordinateEncoding m (d+1) u v N hN (seed, r.1), r.2)

theorem costedCanonicalSampler_value (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (x : Fin k → Bool) :
    (costedCanonicalSampler m d u v k N hk hN x).1 =
      canonicalSampler m d u v k N hk hN x := by
  simp only [costedCanonicalSampler, costedPaddedAND_value, canonicalSampler, graphMap]

theorem costedCanonicalSampler_cost (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (x : Fin k → Bool) :
    (costedCanonicalSampler m d u v k N hk hN x).2 = m*d :=
  costedPaddedAND_cost m d u v (splitSeed m (d+1) u k hk x)

/-- The implemented sampler uses at most k and hence at most N field multiplications. -/
theorem costedCanonicalSampler_cost_bound (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (x : Fin k → Bool) :
    (costedCanonicalSampler m d u v k N hk hN x).2 ≤ k ∧ k ≤ N := by
  rw [costedCanonicalSampler_cost]
  constructor <;> nlinarith

theorem costedCanonicalSampler_is_polynomial (m d u v k N : ℕ)
    (hk : m*(d+1)+u=k) (hN : m*(d+1)+u+(m+v)=N) (x : Fin k → Bool) :
    (costedCanonicalSampler m d u v k N hk hN x).1 =
      (canonicalANDSource m d u v k N hk hN).boolEval (fun j => boolEquivF₂ (x j)) := by
  rw [costedCanonicalSampler_value, canonicalSampler_is_polynomial]

end SamplingLowerBounds.PolynomialModel
