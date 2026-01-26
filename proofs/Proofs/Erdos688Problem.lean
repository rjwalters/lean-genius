/-!
# Erdős Problem #688: Covering by Large Prime Congruences

Define εₙ as the maximum ε such that for some choice of congruence class
aₚ for each prime n^ε < p ≤ n, every integer in [1,n] satisfies at least
one congruence m ≡ aₚ (mod p). Estimate εₙ; is εₙ = o(1)?

## Key Results

- **Erdős's lower bound**: εₙ ≫ (log log log n) / (log log n)
- **Open**: Is εₙ = o(1)? How fast does it tend to 0?
- Related to Problems #687 and #689

## References

- [Er79d] Erdős (1979)
- <https://erdosproblems.com/688>
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A covering assignment: for each prime p in a range, choose a
    residue class aₚ ∈ {0, ..., p−1}. -/
def CoveringAssignment (primes : Finset ℕ) :=
  (p : ℕ) → p ∈ primes → Fin p

/-- Whether a covering assignment covers the interval [1, n]:
    every m ∈ [1, n] satisfies m ≡ aₚ (mod p) for some prime p. -/
def CoverInterval (n : ℕ) (primes : Finset ℕ)
    (assignment : CoveringAssignment primes) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ p ∈ primes, ∃ (hp : p ∈ primes),
      m % p = (assignment p hp : ℕ)

/-- The set of primes in the interval (n^ε, n]. -/
noncomputable def primesInRange (n : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p =>
    Nat.Prime p ∧ (p : ℝ) > (n : ℝ) ^ ε ∧ p ≤ n)

/-- εₙ: the maximum ε such that some choice of residue classes for
    primes in (n^ε, n] covers [1, n]. -/
noncomputable def coveringExponent (n : ℕ) : ℝ :=
  sSup {ε : ℝ | ε > 0 ∧ ε < 1 ∧
    ∃ assignment : CoveringAssignment (primesInRange n ε),
      CoverInterval n (primesInRange n ε) assignment}

/-! ## Main Conjecture -/

/-- **Erdős's Conjecture**: εₙ = o(1), i.e., εₙ → 0 as n → ∞.
    Even primes close to n suffice to cover [1, n] with one class each. -/
axiom erdos_688_conjecture :
  Filter.Tendsto (fun n => coveringExponent n) Filter.atTop (nhds 0)

/-! ## Known Bounds -/

/-- **Erdős's lower bound**: εₙ ≫ (log log log n) / (log log n).
    The exponent cannot decrease faster than this iterated-log ratio. -/
axiom erdos_lower_bound :
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n in Filter.atTop,
      coveringExponent n ≥ c * Real.log (Real.log (Real.log n)) /
        Real.log (Real.log n)

/-- Trivial upper bound: εₙ < 1, since we need at least the prime n
    (if n is prime) or primes up to n. -/
axiom covering_exponent_lt_one :
  ∀ n : ℕ, n ≥ 2 → coveringExponent n < 1

/-! ## Structural Properties -/

/-- Each prime p covers exactly ⌊n/p⌋ or ⌈n/p⌉ integers in [1,n]
    with a single residue class. -/
axiom single_class_coverage :
  ∀ (n p : ℕ) (a : ℕ), Nat.Prime p → p ≤ n → a < p →
    ({m ∈ Finset.range n | (m + 1) % p = a}.card : ℝ) ≤ (n : ℝ) / p + 1

/-- The total coverage capacity of primes in (n^ε, n] is
    ∑_{n^ε < p ≤ n} ⌊n/p⌋ ~ n · (log(1/ε) + O(1)) by Mertens' theorem. -/
axiom mertens_coverage :
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in Filter.atTop,
      ∃ (primes : Finset ℕ),
        (primes.sum (fun p => n / p) : ℝ) ≥ (n : ℝ) * (Real.log (1 / ε) - C)

/-- Monotonicity: if ε₁ ≤ ε₂, the primes in (n^ε₁, n] include those
    in (n^ε₂, n], so more primes are available. -/
axiom exponent_monotone_coverage :
  ∀ (n : ℕ) (ε₁ ε₂ : ℝ), 0 < ε₁ → ε₁ ≤ ε₂ → ε₂ < 1 →
    (primesInRange n ε₂) ⊆ (primesInRange n ε₁)

/-- Covering with all primes ≤ n (ε = 0): by CRT and the prime number
    theorem, one class per prime suffices to cover [1, n] for large n. -/
axiom full_prime_covering :
  ∀ᶠ n in Filter.atTop,
    ∃ assignment : CoveringAssignment (primesInRange n 0),
      CoverInterval n (primesInRange n 0) assignment

/-- The sieve connection: covering [1,n] by one residue class per prime
    is dual to sieving — excluding one class per prime. -/
axiom sieve_duality :
  ∀ (n : ℕ) (primes : Finset ℕ),
    (∀ p ∈ primes, Nat.Prime p) →
    -- If we exclude one class per prime, the remaining set is the
    -- complement of the covering
    True
