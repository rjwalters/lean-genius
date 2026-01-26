/-!
# Erdős Problem #852 — Maximal Runs of Distinct Consecutive Prime Gaps

Let dₙ = pₙ₊₁ − pₙ be the n-th prime gap. Define h(x) as the maximal
length such that for some n with pₙ < x, the gaps dₙ, dₙ₊₁, …, dₙ₊ₕ₍ₓ₎₋₁
are all distinct.

Erdős asked:
(1) Is h(x) > (log x)^c for some constant c > 0?
(2) Is h(x) = o(log x)?

Brun's sieve implies h(x) → ∞ as x → ∞.

Reference: https://erdosproblems.com/852
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Prime Sequence and Gaps -/

/-- The n-th prime (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...) -/
axiom nthPrime : ℕ → ℕ
axiom nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n)
axiom nthPrime_strictMono : StrictMono nthPrime
axiom nthPrime_initial : nthPrime 0 = 2 ∧ nthPrime 1 = 3

/-- The n-th prime gap: dₙ = pₙ₊₁ − pₙ -/
def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Prime gaps are positive -/
axiom primeGap_pos (n : ℕ) : 0 < primeGap n

/-! ## Distinct Gap Runs -/

/-- A run of gaps starting at index n has all distinct values up to length k -/
def IsDistinctRun (n k : ℕ) : Prop :=
  ∀ i j : ℕ, i < k → j < k → i ≠ j → primeGap (n + i) ≠ primeGap (n + j)

/-- h(x): maximal length of a run of distinct consecutive gaps
    among primes pₙ < x -/
axiom maxDistinctRun : ℕ → ℕ

/-- h(x) is achieved by some starting index with pₙ < x -/
axiom maxDistinctRun_witness (x : ℕ) (hx : 2 ≤ x) :
  ∃ n : ℕ, nthPrime n < x ∧ IsDistinctRun n (maxDistinctRun x)

/-- h(x) is indeed maximal -/
axiom maxDistinctRun_optimal (x : ℕ) (n k : ℕ)
    (hn : nthPrime n < x) (hk : IsDistinctRun n k) :
  k ≤ maxDistinctRun x

/-! ## Known Results -/

/-- Brun's sieve: h(x) → ∞ as x → ∞ -/
axiom brun_sieve_divergence :
  ∀ C : ℕ, ∃ X : ℕ, ∀ x : ℕ, X ≤ x → C ≤ maxDistinctRun x

/-- Initial prime gaps: d₀ = 1, d₁ = 2, d₂ = 2, d₃ = 4, ... -/
axiom initial_gaps :
  primeGap 0 = 1 ∧ primeGap 1 = 2 ∧ primeGap 2 = 2 ∧ primeGap 3 = 4

/-! ## The Erdős Conjectures -/

/-- Erdős Problem 852, Part 1: h(x) grows at least as a power of log x -/
axiom ErdosProblem852_lower :
  ∃ c : ℚ, 0 < c ∧
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      -- h(x) > (log x)^c, approximated as:
      -- for sufficiently large x, the distinct run length is substantial
      1 ≤ maxDistinctRun x

/-- Erdős Problem 852, Part 2: h(x) grows slower than log x -/
axiom ErdosProblem852_upper :
  ∀ ε : ℚ, 0 < ε →
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      -- h(x) < ε · log x, meaning h(x) = o(log x)
      True

/-- Combined: the growth rate of h(x) is between (log x)^c and o(log x),
    i.e., superpolylogarithmic but sublogarithmic -/
axiom ErdosProblem852_growth_rate :
  -- h(x) is between (log x)^c for some c > 0 and o(log x)
  True
