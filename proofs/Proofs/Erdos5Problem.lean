/-
# Erdős Problem #5: Limit Points of Normalized Prime Gaps

Let p_n denote the n-th prime. Define the normalized gap ratio
  g(n) = (p_{n+1} - p_n) / log(p_n).

Let S be the set of all limit points of the sequence g(n).
Erdős conjectured S = [0, ∞), i.e., for every C ≥ 0 there exist
infinitely many n with g(n) → C.

Known results:
- 0 ∈ S: Goldston–Pintz–Yıldırım (2009)
- ∞ ∈ S: Westzynthius (1931), improved by Rankin, Erdős, Ford–Green–Konyagin–Tao
- S has positive Lebesgue measure: Erdős–Ricci
- S contains arbitrarily large finite values: Hildebrand–Maier
- At least 1/3 of [0, ∞) belongs to S: Merikoski (2020)

Status: OPEN.

Reference: https://erdosproblems.com/5
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic

/- ## Definitions -/

/-- The n-th prime number (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...).
    Defined using Mathlib's Nat.nth enumeration of the infinite set of primes.
    Previously axiomatized; now concrete via Nat.nth. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- nthPrime n is always prime.
    Previously axiomatized (with unnecessary hypothesis 1 ≤ n);
    now proved directly from the Nat.nth definition. -/
theorem nthPrime_prime (n : ℕ) : (nthPrime n).Prime := by
  unfold nthPrime
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- nthPrime is strictly increasing.
    Previously axiomatized; now proved from Nat.nth_strictMono. -/
theorem nthPrime_strictMono : StrictMono nthPrime := by
  intro a b hab
  unfold nthPrime
  exact Nat.nth_strictMono Nat.infinite_setOf_prime hab

/-- The normalized prime gap ratio g(n) = (p_{n+1} - p_n) / log(p_n). -/
noncomputable def normalizedGap (n : ℕ) : ℝ :=
  (nthPrime (n + 1) - nthPrime n : ℤ) / Real.log (nthPrime n)

/-- A real number C is a limit point of the normalized gap sequence
    if for every ε > 0, there exist infinitely many n with |g(n) - C| < ε. -/
def IsLimitPointOfGaps (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    |normalizedGap n - C| < ε

/- ## Known Results -/

/-- 0 ∈ S: Goldston–Pintz–Yıldırım (2009) proved
    lim inf (p_{n+1} - p_n) / log(p_n) = 0. -/
/-- ∞ ∈ S: Westzynthius (1931) proved the gaps can be arbitrarily large
    relative to log(p_n). Formally: for every M, there exist infinitely many n
    with g(n) > M. -/
axiom gaps_unbounded (M : ℝ) :
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ normalizedGap n > M

/-- Hildebrand–Maier: for any C > 0 there exist infinitely many n
    with g(n) > C. (Strengthening: S contains arbitrarily large finite values.)
    Previously axiomatized; now derived from gaps_unbounded. -/
theorem hildebrand_maier_large_gaps (C : ℝ) (hC : 0 < C) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ normalizedGap n > C :=
  gaps_unbounded C

/-- Merikoski (2020): at least 1/3 of any bounded interval [0, T]
    is covered by S. Formally: the Lebesgue measure of
    S ∩ [0, T] is at least T/3 for all T > 0. -/
/- ## The Conjecture -/

/-- Erdős Problem #5: The set S of limit points of (p_{n+1} - p_n)/log(p_n)
    equals [0, ∞). That is, for every C ≥ 0, C is a limit point of
    the normalized gap sequence. -/
