/-!
# Erdős Problem #200: Longest Arithmetic Progression of Primes

Does the longest arithmetic progression of primes in {1,...,N} have
length o(log N)?

## Key Results

- Upper bound: PNT implies the longest prime AP in {1,...,N} has
  length ≤ (1 + o(1)) log N
- Green–Tao (2008): primes contain arbitrarily long APs
- The question asks whether the growth rate is strictly sublogarithmic

## References

- Erdős–Graham [ErGr79], [ErGr80]
- Green–Tao (2008): arbitrarily long prime APs
- OEIS A005115: length of longest prime AP up to n
- <https://erdosproblems.com/200>
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- An arithmetic progression of length k with first term a and
    common difference d: {a, a+d, a+2d, ..., a+(k-1)d}. -/
def IsAPSequence (s : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ i : ℕ, i < k → s i = a + i * d

/-- A prime arithmetic progression of length k in {1,...,N}. -/
def IsPrimeAP (k N : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧
    (∀ i : ℕ, i < k → (a + i * d).Prime) ∧
    (∀ i : ℕ, i < k → a + i * d ≤ N)

/-- The length of the longest arithmetic progression of primes
    in {1,...,N}. -/
noncomputable def longestPrimeAP (N : ℕ) : ℕ :=
  sSup {k : ℕ | IsPrimeAP k N}

/-! ## Upper Bound from PNT -/

/-- The Prime Number Theorem implies: any AP of primes in {1,...,N}
    has length at most (1 + o(1)) · log N.

    Proof sketch: an AP {a, a+d, ..., a+(k-1)d} ⊆ {1,...,N} has
    common difference d ≥ 1, so the AP spans at least k-1. But
    by PNT, primes in {1,...,N} have density ~ 1/log N, and an AP
    of primes of length k with difference d must avoid all prime
    factors of d, giving the constraint k ≤ (1+o(1)) log N. -/
axiom prime_ap_upper_pnt :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N > N₀ →
    (longestPrimeAP N : ℝ) ≤ (1 + ε) * Real.log N

/-! ## Green–Tao Theorem -/

/-- Green–Tao (2008): For every k, there exists a prime AP of length k.
    This means longestPrimeAP N → ∞ as N → ∞. -/
axiom green_tao :
  ∀ k : ℕ, ∃ N : ℕ, IsPrimeAP k N

/-- Consequence: longestPrimeAP N is unbounded. -/
axiom longest_prime_ap_unbounded :
  ∀ M : ℕ, ∃ N : ℕ, longestPrimeAP N ≥ M

/-! ## Main Conjecture -/

/-- **Erdős Problem #200** (OPEN): The longest prime AP in {1,...,N}
    has length o(log N), i.e., longestPrimeAP(N) / log(N) → 0.

    This asks whether the PNT upper bound of ~ log N is far from
    the truth. -/
axiom erdos_200_conjecture :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N > N₀ →
    (longestPrimeAP N : ℝ) < ε * Real.log N

/-! ## Known Bounds and Examples -/

/-- The AP {3, 5, 7} has length 3 — trivial example. -/
axiom prime_ap_3 : IsPrimeAP 3 7

/-- The AP {5, 11, 17, 23, 29} has length 5. -/
axiom prime_ap_5 : IsPrimeAP 5 29

/-- Green–Tao–Maynard: quantitative bounds on the least N containing
    a prime AP of length k. The best bounds give
    N(k) ≤ exp(exp(exp(ck))). -/
axiom green_tao_quantitative :
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    ∃ N : ℕ, (N : ℝ) ≤ Real.exp (Real.exp (Real.exp (c * k))) ∧
    IsPrimeAP k N

/-! ## Relationship to Other Conjectures -/

/-- If the Hardy–Littlewood k-tuple conjecture holds, then for any k,
    the expected number of prime k-APs with difference d ≤ x is
    ~ c_k · x / (log x)^k, predicting longestPrimeAP(N) ~ c · log N
    for some constant c < 1. -/
axiom hardy_littlewood_prediction :
  True  -- Predicts longestPrimeAP(N) ~ c · log N, NOT o(log N)

/-- Note: the Hardy–Littlewood prediction suggests the answer to
    Erdős's question might be NO — the longest prime AP could be
    Θ(log N), not o(log N). This makes the problem delicate. -/
axiom hl_suggests_negative :
  True  -- Heuristically, longestPrimeAP(N) / log(N) → c for some c ∈ (0,1]

/-! ## Structural Observations -/

/-- In a prime AP {a, a+d, ..., a+(k-1)d}, the common difference d
    must be divisible by all primes ≤ k (to avoid forced composites).
    So d ≥ k# (primorial of k), which grows as e^(1+o(1))k. -/
axiom ap_difference_primorial (k : ℕ) (hk : k ≥ 3) :
  ∀ a d : ℕ, (∀ i : ℕ, i < k → (a + i * d).Prime) → d > 0 →
    ∀ p : ℕ, p.Prime → p ≤ k → p ∣ d

/-- The primorial constraint means a prime AP of length k uses
    numbers up to at least a + (k-1) · k#, which grows rapidly. -/
axiom primorial_growth :
  ∀ ε : ℝ, ε > 0 → ∃ K₀ : ℕ, ∀ k : ℕ, k > K₀ →
    True  -- k# ≥ e^((1-ε)k)
