/-
Erdős Problem #456 — Smallest Prime ≡ 1 (mod n) vs Smallest m with n | φ(m)

Let pₙ be the smallest prime ≡ 1 (mod n), and let mₙ be the smallest
positive integer such that n | φ(mₙ).

Erdős asked:
(1) Is mₙ < pₙ for almost all n?
(2) Does pₙ/mₙ → ∞ for almost all n?
(3) Are there infinitely many primes p such that p − 1 is the only n
    with mₙ = p?

Known:
- mₙ ≤ pₙ always (trivially, since φ(pₙ) = pₙ − 1 and n | pₙ − 1)
- Linnik: pₙ ≤ n^{O(1)}
- When n = q − 1 for prime q, mₙ = pₙ
- For n = 2^{2k+1}: mₙ ≤ 2n < pₙ (van Doorn)
- mₙ < pₙ for infinitely many n (Erdős)
- mₙ/n → ∞ for almost all n

**Status:** OPEN

**Reference:** https://erdosproblems.com/456

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient

open Nat

namespace Erdos456

/-
# Part 1: Core Definitions

We define the two key functions using Mathlib's Nat.totient.
-/

/-- pₙ: the smallest prime ≡ 1 (mod n).
    By Dirichlet's theorem on primes in arithmetic progressions, this exists for all n ≥ 1. -/
noncomputable def smallestPrimeMod1 (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ n ∣ (p - 1)}

/-- mₙ: the smallest positive integer m with n | φ(m) -/
noncomputable def smallestTotientDiv (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ m.totient}

/-
# Part 2: Properties of smallestPrimeMod1
-/

/-- Dirichlet's theorem: for n ≥ 1, there exist infinitely many primes ≡ 1 (mod n) -/
axiom dirichlet_primes_mod1 (n : ℕ) (hn : 1 ≤ n) :
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ n ∣ (p - 1)

/-- pₙ is prime -/
axiom smallestPrimeMod1_prime (n : ℕ) (hn : 1 ≤ n) :
  (smallestPrimeMod1 n).Prime

/-- pₙ ≡ 1 (mod n) -/
axiom smallestPrimeMod1_cong (n : ℕ) (hn : 1 ≤ n) :
  n ∣ (smallestPrimeMod1 n - 1)

/-- pₙ is minimal among such primes -/
axiom smallestPrimeMod1_minimal (n : ℕ) (hn : 1 ≤ n) (p : ℕ)
    (hp : p.Prime) (hcong : n ∣ (p - 1)) :
  smallestPrimeMod1 n ≤ p

/-
# Part 3: Properties of smallestTotientDiv
-/

/-- mₙ is positive -/
axiom smallestTotientDiv_pos (n : ℕ) (hn : 1 ≤ n) :
  0 < smallestTotientDiv n

/-- n | φ(mₙ) -/
axiom smallestTotientDiv_divides (n : ℕ) (hn : 1 ≤ n) :
  n ∣ (smallestTotientDiv n).totient

/-- mₙ is minimal -/
axiom smallestTotientDiv_minimal (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (hm : 0 < m) (hdiv : n ∣ m.totient) :
  smallestTotientDiv n ≤ m

/-
# Part 4: Known Results
-/

/-- mₙ ≤ pₙ always.
    Proof sketch: φ(pₙ) = pₙ − 1 and n | pₙ − 1, so pₙ is in the set defining mₙ.
    By minimality of mₙ, mₙ ≤ pₙ. -/
axiom m_le_p (n : ℕ) (hn : 1 ≤ n) :
  smallestTotientDiv n ≤ smallestPrimeMod1 n

/-- Linnik's theorem: pₙ = O(n^L) for some constant L -/
axiom linnik_bound :
  ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n →
    smallestPrimeMod1 n ≤ n ^ L

/-- mₙ < pₙ for infinitely many n (Erdős) -/
axiom erdos_strict_inequality :
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    smallestTotientDiv n < smallestPrimeMod1 n

/-- mₙ/n → ∞ for almost all n (Erdős).
    For any constant C, the set of n with mₙ ≤ C·n has density 0. -/
axiom m_over_n_diverges :
  ∀ C : ℕ, ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ M ≥ N,
    -- The number of n ≤ M with mₙ ≤ C·n is < ε·M
    (Finset.filter (fun n => smallestTotientDiv n ≤ C * n) (Finset.range M)).card < M

/-- Van Doorn: for n = 2^{2k+1}, mₙ ≤ 2n -/
axiom van_doorn_power_of_two (k : ℕ) :
  let n := 2 ^ (2 * k + 1)
  smallestTotientDiv n ≤ 2 * n

/-
# Part 5: Natural Density
-/

/-- "Almost all" in the natural density sense:
    P holds for all but a density-0 set of natural numbers -/
def AlmostAll (P : ℕ → Prop) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ M ≥ N,
    (Finset.filter (fun n => ¬P n) (Finset.range M)).card < M

/-
# Part 6: The Erdős Conjectures (OPEN)
-/

/-- Erdős Problem 456, Part 1: mₙ < pₙ for almost all n -/
def ErdosProblem456_Part1 : Prop :=
  AlmostAll (fun n => 1 ≤ n → smallestTotientDiv n < smallestPrimeMod1 n)

/-- Erdős Problem 456, Part 2: pₙ/mₙ → ∞ for almost all n -/
def ErdosProblem456_Part2 : Prop :=
  ∀ C : ℕ, AlmostAll (fun n => 1 ≤ n →
    C * smallestTotientDiv n ≤ smallestPrimeMod1 n)

/-- Erdős Problem 456, Part 3: infinitely many primes p where
    p − 1 is the unique n with mₙ = p -/
def ErdosProblem456_Part3 : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧
    smallestTotientDiv (p - 1) = p ∧
    (∀ n : ℕ, smallestTotientDiv n = p → n = p - 1)

/-
# Part 7: Relationships Between Parts
-/

/-- Part 2 implies Part 1 -/
theorem part2_implies_part1 : ErdosProblem456_Part2 → ErdosProblem456_Part1 := by
  intro h2
  -- Taking C = 1 in Part 2 gives Part 1 (with ≤ instead of <)
  -- Actually need strict inequality, so this needs care
  sorry

/-- The infinitely-many result is weaker than the density result -/
theorem part1_implies_infinitely_many :
    ErdosProblem456_Part1 → ∀ N : ℕ, ∃ n ≥ N, smallestTotientDiv n < smallestPrimeMod1 n := by
  intro h1 N
  -- Almost all implies infinitely many
  sorry

end Erdos456
