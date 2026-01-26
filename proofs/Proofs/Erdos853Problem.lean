/-!
# Erdős Problem #853: Smallest Missing Prime Gap

Let d_n = p_{n+1} - p_n be the n-th prime gap. Let r(x) be the smallest
even integer t such that d_n = t has no solution for p_n ≤ x.
Is it true that r(x) → ∞? Or even r(x) / log x → ∞?

## Key Results

- The even restriction is necessary since all prime gaps > 1 are even
- Maynard–Tao (2014): bounded gaps — infinitely many d_n ≤ 246
- Zhang (2013): bounded gaps — infinitely many d_n ≤ 70,000,000
- The question asks about the completeness of gap sizes up to x

## References

- Erdős [Er85c]
- OEIS A001223 (prime gaps), A390769
- <https://erdosproblems.com/853>
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The n-th prime (1-indexed): p(1) = 2, p(2) = 3, p(3) = 5, ... -/
axiom nthPrime (n : ℕ) : ℕ

/-- nthPrime returns primes. -/
axiom nthPrime_prime (n : ℕ) (hn : n ≥ 1) : (nthPrime n).Prime

/-- nthPrime is strictly increasing. -/
axiom nthPrime_strictMono : StrictMono nthPrime

/-- The n-th prime gap: d_n = p_{n+1} - p_n. -/
def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- The set of prime gaps occurring for primes up to x:
    { d_n : p_n ≤ x }. -/
def gapSet (x : ℕ) : Set ℕ :=
  {t : ℕ | ∃ n : ℕ, n ≥ 1 ∧ nthPrime n ≤ x ∧ primeGap n = t}

/-- r(x): smallest positive even integer not in the gap set up to x. -/
noncomputable def smallestMissingGap (x : ℕ) : ℕ :=
  Nat.find ⟨x + 2, by omega⟩  -- trivially bounded; actual definition below

/-- Axiomatized r(x): smallest even t ≥ 2 with no d_n = t for p_n ≤ x. -/
axiom r (x : ℕ) : ℕ

/-- r(x) is even and positive. -/
axiom r_even_pos (x : ℕ) (hx : x ≥ 2) : r x ≥ 2 ∧ r x % 2 = 0

/-- r(x) is not a gap: no prime p_n ≤ x has gap d_n = r(x). -/
axiom r_not_gap (x : ℕ) (hx : x ≥ 2) :
  ¬∃ n : ℕ, n ≥ 1 ∧ nthPrime n ≤ x ∧ primeGap n = r x

/-- r(x) is minimal: every even t with 2 ≤ t < r(x) appears as a gap. -/
axiom r_minimal (x : ℕ) (hx : x ≥ 2) :
  ∀ t : ℕ, 2 ≤ t → t < r x → t % 2 = 0 →
    ∃ n : ℕ, n ≥ 1 ∧ nthPrime n ≤ x ∧ primeGap n = t

/-! ## Main Conjectures -/

/-- **Erdős Problem #853, Weak Form** (OPEN): r(x) → ∞ as x → ∞.
    Every even gap size eventually appears among prime gaps. -/
axiom erdos_853_weak :
  ∀ M : ℕ, ∃ X : ℕ, ∀ x : ℕ, x ≥ X → r x ≥ M

/-- **Erdős Problem #853, Strong Form** (OPEN): r(x) / log x → ∞.
    The smallest missing gap grows faster than logarithmically. -/
axiom erdos_853_strong :
  ∀ C : ℝ, C > 0 → ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
    (r x : ℝ) ≥ C * Real.log x

/-! ## Related Results -/

/-- All prime gaps > 1 are even (since p > 2 implies p is odd,
    and consecutive odd primes differ by an even number). -/
axiom prime_gap_even (n : ℕ) (hn : n ≥ 2) :
  primeGap n % 2 = 0

/-- Maynard–Tao (2014): there are infinitely many n with d_n ≤ 246.
    This means gap = 2 (or some small even value) appears infinitely often. -/
axiom maynard_tao_bounded_gaps :
  ∃ t : ℕ, t ≤ 246 ∧ t % 2 = 0 ∧
    ∀ X : ℕ, ∃ n : ℕ, nthPrime n > X ∧ primeGap n = t

/-- Cramér's conjecture: the largest prime gap below x is O((log x)²).
    This implies r(x) ≤ O((log x)²) if all smaller even gaps also appear. -/
axiom cramer_conjecture_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 2 →
    (r x : ℝ) ≤ C * (Real.log x) ^ 2

/-! ## Monotonicity and Growth -/

/-- r is (weakly) monotone increasing: as x grows, more gaps appear. -/
axiom r_monotone : ∀ x y : ℕ, x ≤ y → r x ≤ r y

/-- Trivial upper bound: r(x) ≤ x since all gaps are < x. -/
axiom r_trivial_upper (x : ℕ) (hx : x ≥ 2) : r x ≤ x

/-- The gap d_1 = p_2 - p_1 = 3 - 2 = 1 is the only odd gap.
    After d_1, all gaps are even. -/
axiom first_gap_odd : primeGap 1 = 1
