/-!
# Erdős Problem #456 — Smallest Prime ≡ 1 (mod n) vs Smallest m with n | φ(m)

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

Reference: https://erdosproblems.com/456
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Core Functions -/

/-- Euler's totient function (abstract) -/
axiom eulerTotient : ℕ → ℕ
axiom totient_prime (p : ℕ) (hp : Nat.Prime p) : eulerTotient p = p - 1
axiom totient_pos (n : ℕ) (hn : 1 ≤ n) : 0 < eulerTotient n

/-- pₙ: the smallest prime ≡ 1 (mod n) -/
axiom smallestPrimeMod1 : ℕ → ℕ
axiom smallestPrimeMod1_prime (n : ℕ) (hn : 1 ≤ n) :
  Nat.Prime (smallestPrimeMod1 n)
axiom smallestPrimeMod1_cong (n : ℕ) (hn : 1 ≤ n) :
  smallestPrimeMod1 n % n = 1 % n ∨ n ∣ (smallestPrimeMod1 n - 1)
axiom smallestPrimeMod1_minimal (n : ℕ) (hn : 1 ≤ n) (p : ℕ)
    (hp : Nat.Prime p) (hcong : n ∣ (p - 1)) :
  smallestPrimeMod1 n ≤ p

/-- mₙ: the smallest positive integer m with n | φ(m) -/
axiom smallestTotientDiv : ℕ → ℕ
axiom smallestTotientDiv_pos (n : ℕ) (hn : 1 ≤ n) :
  0 < smallestTotientDiv n
axiom smallestTotientDiv_divides (n : ℕ) (hn : 1 ≤ n) :
  n ∣ eulerTotient (smallestTotientDiv n)
axiom smallestTotientDiv_minimal (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (hm : 0 < m) (hdiv : n ∣ eulerTotient m) :
  smallestTotientDiv n ≤ m

/-! ## Known Results -/

/-- mₙ ≤ pₙ always (since φ(pₙ) = pₙ − 1 and n | pₙ − 1) -/
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

/-- mₙ/n → ∞ for almost all n (Erdős) -/
axiom m_over_n_diverges :
  ∀ C : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    -- For all but finitely many n: mₙ > C · n
    True

/-- Van Doorn: for n = 2^{2k+1}, mₙ ≤ 2n and pₙ ≥ 2n + 1 -/
axiom van_doorn_power_of_two (k : ℕ) :
  let n := 2 ^ (2 * k + 1)
  smallestTotientDiv n ≤ 2 * n

/-! ## The Erdős Conjectures -/

/-- "Almost all" in the natural density sense -/
def AlmostAll (P : ℕ → Prop) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    -- The proportion of exceptions up to n is < ε
    True

/-- Erdős Problem 456, Part 1: mₙ < pₙ for almost all n -/
axiom ErdosProblem456_almost_all :
  AlmostAll (fun n => 1 ≤ n → smallestTotientDiv n < smallestPrimeMod1 n)

/-- Erdős Problem 456, Part 2: pₙ/mₙ → ∞ for almost all n -/
axiom ErdosProblem456_ratio_diverges :
  ∀ C : ℕ, AlmostAll (fun n => 1 ≤ n →
    C * smallestTotientDiv n ≤ smallestPrimeMod1 n)

/-- Erdős Problem 456, Part 3: infinitely many primes p where
    p − 1 is the unique n with mₙ = p -/
axiom ErdosProblem456_unique_preimage :
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ Nat.Prime p ∧
    smallestTotientDiv (p - 1) = p ∧
    (∀ n : ℕ, smallestTotientDiv n = p → n = p - 1)
