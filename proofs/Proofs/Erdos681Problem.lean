/-!
# Erdős Problem 681: Large Least Prime Factor in Shifted Composites

For all sufficiently large `n`, does there exist a positive integer `k`
such that `n + k` is composite and `p(n + k) > k²`, where `p(m)` is
the least prime factor of `m`?

A generalisation asks whether `p(n + k) > k^d` for any fixed `d`.

Posed by Erdős, Eggleton, and Selfridge.

*Reference:* [erdosproblems.com/681](https://www.erdosproblems.com/681)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Least prime factor -/

/-- The least prime factor of `m`, using `Nat.minFac`. Returns 1 if
`m ≤ 1`. -/
noncomputable def leastPrimeFactor (m : ℕ) : ℕ :=
    if m ≤ 1 then 1 else m.minFac

/-- `p` is the least prime factor of `m`. -/
def IsLeastPrimeFactor (p m : ℕ) : Prop :=
    p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q

/-- A composite number has a least prime factor that is prime. -/
axiom composite_has_lpf (m : ℕ) (hm : ¬m.Prime) (hm2 : 2 ≤ m) :
    ∃ p : ℕ, IsLeastPrimeFactor p m

/-! ## The conjecture -/

/-- Erdős Problem 681: For all sufficiently large `n`, there exists
`k > 0` such that `n + k` is composite and its least prime factor
exceeds `k²`. -/
def ErdosProblem681 : Prop :=
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 0 < k ∧
        ¬(n + k).Prime ∧ 2 ≤ n + k ∧
        ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p

/-! ## Generalisation -/

/-- Generalised conjecture: for any fixed `d`, for all large `n`,
there exists `k > 0` with `n + k` composite and `p(n+k) > k^d`. -/
def ErdosProblem681General (d : ℕ) : Prop :=
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 0 < k ∧
        ¬(n + k).Prime ∧ 2 ≤ n + k ∧
        ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ d < p

/-- The original conjecture is the `d = 2` case. -/
axiom erdos681_is_general_d2 :
    ErdosProblem681 ↔ ErdosProblem681General 2

/-! ## Basic observations -/

/-- If `n + k` is prime, it trivially has least prime factor `n + k`
itself, which is large. The conjecture requires `n + k` composite. -/
axiom prime_lpf_self (p : ℕ) (hp : p.Prime) :
    IsLeastPrimeFactor p p

/-- The least prime factor of a composite `m` satisfies
`p(m) ≤ √m`. -/
axiom lpf_le_sqrt (m : ℕ) (hm : ¬m.Prime) (hm2 : 2 ≤ m) :
    ∃ p : ℕ, IsLeastPrimeFactor p m ∧ p * p ≤ m

/-- `Nat.minFac` gives the least prime factor for `m ≥ 2`. -/
axiom minFac_is_lpf (m : ℕ) (hm : 2 ≤ m) :
    IsLeastPrimeFactor m.minFac m
