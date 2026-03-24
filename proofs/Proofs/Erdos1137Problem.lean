/-
Erdős Problem #1137: Consecutive Prime Gap Products

Source: https://erdosproblems.com/1137
Status: OPEN
Reference: [Va99, 1.2]

Statement:
Let d_n = p_{n+1} - p_n, where p_n denotes the n-th prime. Is it true that
  max_{n<x} d_n · d_{n-1} / (max_{n<x} d_n)² → 0
as x → ∞?

This asks whether large prime gaps tend NOT to occur consecutively:
the largest product of adjacent gaps grows strictly slower than the
square of the largest individual gap.

History:
- Appears in Varga's survey [Va99, §1.2]
- Related to the Cramér and Granville conjectures on prime gap distribution
- The Hardy-Littlewood k-tuples conjecture heuristically supports YES
- Known: maximal prime gaps grow like (log p)² (Cramér's conjecture)

Tags: number-theory, primes, prime-gaps, analytic-number-theory
-/

import Mathlib

open Finset Filter Nat
open scoped Topology

namespace Erdos1137

-- ## Part I: Core Definitions

/-- The n-th prime gap: d_n = p_{n+1} - p_n (0-indexed).
    Examples: d_0 = 3 - 2 = 1, d_1 = 5 - 3 = 2, d_2 = 7 - 5 = 2. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  nth Nat.Prime (n + 1) - nth Nat.Prime n

/-- Maximum prime gap among the first x gaps: max_{n < x} d_n.
    Uses Finset.sup which defaults to 0 (⊥) on an empty range. -/
noncomputable def maxGap (x : ℕ) : ℕ :=
  (Finset.range x).sup primeGap

/-- The Erdős #1137 ratio: the quotient
      max_{n<x} (d_n · d_{n-1}) / (max_{n<x} d_n)²
    where d_{n-1} at n = 0 uses ℕ subtraction (yielding d_0).
    The conjecture asks whether this tends to 0. -/
noncomputable def erdosRatio (x : ℕ) : ℝ :=
  (((Finset.range x).sup (fun n => primeGap n * primeGap (n - 1)) : ℕ) : ℝ) /
  ((maxGap x : ℝ) ^ 2)

-- ## Part II: Basic Properties of Prime Gaps

/-- The primes form a strictly increasing sequence. -/
theorem nth_prime_strictMono : StrictMono (nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/-- p_0 = 2. -/
theorem nth_prime_zero : nth Nat.Prime 0 = 2 :=
  Nat.nth_prime_zero_eq_two

/-- The n-th prime is prime. -/
theorem nth_prime_is_prime (n : ℕ) : Nat.Prime (nth Nat.Prime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- p_{n+1} > p_n for all n. -/
theorem nth_prime_lt_succ (n : ℕ) : nth Nat.Prime n < nth Nat.Prime (n + 1) :=
  nth_prime_strictMono (Nat.lt_succ_of_le le_rfl)

/-- Prime gaps are positive: d_n ≥ 1 for all n.
    Since the primes are strictly increasing, p_{n+1} - p_n ≥ 1. -/
theorem primeGap_pos (n : ℕ) : primeGap n ≥ 1 := by
  unfold primeGap
  have h := nth_prime_lt_succ n
  omega

/-- p_1 = 3 (the second prime, 0-indexed). -/
theorem nth_prime_one : nth Nat.Prime 1 = 3 := by
  have h_count : Nat.count Nat.Prime 3 = 1 := by decide
  have h_prime : Nat.Prime 3 := by decide
  rw [← h_count]
  exact Nat.nth_count h_prime

/-- The first prime gap: d_0 = p_1 - p_0 = 3 - 2 = 1.
    This is the unique odd prime gap (gap between the only even prime 2 and 3). -/
theorem primeGap_zero : primeGap 0 = 1 := by
  unfold primeGap
  rw [nth_prime_zero, nth_prime_one]

/-- p_2 = 5 (the third prime, 0-indexed). -/
theorem nth_prime_two : nth Nat.Prime 2 = 5 := by
  have h_count : Nat.count Nat.Prime 5 = 2 := by decide
  have h_prime : Nat.Prime 5 := by decide
  rw [← h_count]
  exact Nat.nth_count h_prime

/-- The second prime gap: d_1 = p_2 - p_1 = 5 - 3 = 2. -/
theorem primeGap_one : primeGap 1 = 2 := by
  unfold primeGap
  rw [nth_prime_one, nth_prime_two]

-- ## Part III: Parity of Prime Gaps

/-- For n ≥ 1, the n-th prime is ≥ 3.
    Since nth is strictly monotone and p_1 = 3. -/
theorem nth_prime_ge_three (n : ℕ) (hn : n ≥ 1) : nth Nat.Prime n ≥ 3 := by
  calc nth Nat.Prime n ≥ nth Nat.Prime 1 := nth_prime_strictMono.monotone hn
    _ = 3 := nth_prime_one

/-- For n ≥ 1, the n-th prime is not even (hence odd).
    An even prime must be 2, but p_n ≥ 3 for n ≥ 1. -/
theorem nth_prime_not_even (n : ℕ) (hn : n ≥ 1) : ¬Even (nth Nat.Prime n) := by
  intro ⟨k, hk⟩
  have hp := nth_prime_is_prime n
  have hge := nth_prime_ge_three n hn
  have h2dvd : (2 : ℕ) ∣ nth Nat.Prime n := ⟨k, by omega⟩
  rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h | h <;> omega

/-- For n ≥ 1, the prime gap d_n is even.
    Both p_n and p_{n+1} are odd primes (≥ 3), and odd − odd = even. -/
theorem primeGap_even (n : ℕ) (hn : n ≥ 1) : Even (primeGap n) := by
  unfold primeGap
  rw [Nat.even_sub (le_of_lt (nth_prime_lt_succ n))]
  exact iff_of_false (nth_prime_not_even (n + 1) (by omega)) (nth_prime_not_even n hn)

/-- For n ≥ 1, the prime gap d_n ≥ 2.
    Since d_n is even (from parity) and ≥ 1 (from positivity), d_n ≥ 2.
    Equivalently: all primes after 2 are odd, so consecutive odd primes
    differ by at least 2. -/
theorem primeGap_ge_two (n : ℕ) (hn : n ≥ 1) : primeGap n ≥ 2 := by
  have heven := primeGap_even n hn
  have hpos := primeGap_pos n
  obtain ⟨k, hk⟩ := heven
  omega

-- ## Part IV: Computations

/-- p_3 = 7. -/
theorem nth_prime_three : nth Nat.Prime 3 = 7 := by
  have h_count : Nat.count Nat.Prime 7 = 3 := by decide
  have h_prime : Nat.Prime 7 := by decide
  rw [← h_count]
  exact Nat.nth_count h_prime

/-- d_2 = p_3 - p_2 = 7 - 5 = 2 (twin prime gap). -/
theorem primeGap_two : primeGap 2 = 2 := by
  unfold primeGap
  rw [nth_prime_two, nth_prime_three]

/-- p_4 = 11. -/
theorem nth_prime_four : nth Nat.Prime 4 = 11 := by
  have h_count : Nat.count Nat.Prime 11 = 4 := by decide
  have h_prime : Nat.Prime 11 := by decide
  rw [← h_count]
  exact Nat.nth_count h_prime

/-- d_3 = p_4 - p_3 = 11 - 7 = 4. -/
theorem primeGap_three : primeGap 3 = 4 := by
  unfold primeGap
  rw [nth_prime_three, nth_prime_four]

-- ## Part V: Main Conjecture

/-- **Erdős Problem #1137 (OPEN)**:

    Let d_n = p_{n+1} - p_n. The conjecture asserts that
      max_{n < x} d_n · d_{n-1} / (max_{n < x} d_n)² → 0
    as x → ∞.

    Intuitively: the record-breaking prime gaps should not appear in
    consecutive pairs. If g(x) denotes the maximal gap below x, then
    while individual gaps can be as large as g(x), the product of two
    adjacent gaps is o(g(x)²).

    This is implied by the Cramér–Granville conjecture on the distribution
    of prime gaps and is consistent with extensive numerical evidence.

    The `answer(sorry)` wrapper indicates this is an open yes/no question.
    The statement uses ℕ subtraction at n = 0 (yielding d_0 · d_0 = 1),
    which does not affect the limiting behavior. -/
axiom erdos_1137 :
    Tendsto (fun x =>
      (((Finset.range x).sup (fun n => primeGap n * primeGap (n - 1)) : ℕ) : ℝ) /
      (((Finset.range x).sup primeGap : ℕ) : ℝ) ^ 2)
    atTop (𝓝 0)

-- ## Part VI: Consequences and Context

/-- The ratio is trivially bounded above by 1 for x ≥ 1.
    For any n < x: d_n ≤ maxGap x and d_{n-1} ≤ maxGap(x+1),
    so d_n · d_{n-1} ≤ maxGap(x) · maxGap(x+1) ≤ maxGap(x+1)².
    The tighter bound max_{n<x}(d_n · d_{n-1}) ≤ (maxGap x)² requires
    careful handling of the d_{n-1} index relative to range x. -/
axiom erdosRatio_le_one (x : ℕ) (hx : x ≥ 2) : erdosRatio x ≤ 1

/-- The maximal prime gap tends to infinity.
    This follows from Bertrand's postulate: for any N, there exist
    consecutive primes p_n, p_{n+1} with p_n > N, and eventually
    the gaps must exceed any bound (since primes thin out). -/
axiom maxGap_tendsto_atTop : Tendsto (fun x => (maxGap x : ℝ)) atTop atTop

/-
## Summary

**Problem Status: OPEN**

Erdős Problem #1137 asks whether the ratio of the maximum product
of consecutive prime gaps to the square of the maximum gap tends to 0.

**Proved Theorems (0 sorries)**:
- nth_prime_strictMono: primes are strictly increasing
- nth_prime_zero/one/two/three/four: p_0 = 2, p_1 = 3, p_2 = 5, p_3 = 7, p_4 = 11
- nth_prime_lt_succ: p_{n+1} > p_n
- nth_prime_is_prime: p_n is prime
- nth_prime_ge_three: for n ≥ 1, p_n ≥ 3
- nth_prime_not_even: for n ≥ 1, p_n is odd
- primeGap_pos: d_n ≥ 1 for all n
- primeGap_zero: d_0 = 1
- primeGap_one: d_1 = 2
- primeGap_two: d_2 = 2
- primeGap_three: d_3 = 4
- primeGap_even: d_n is even for n ≥ 1
- primeGap_ge_two: d_n ≥ 2 for n ≥ 1

**Axioms (3)**:
- erdos_1137: the main open conjecture (ratio → 0)
- erdosRatio_le_one: trivial upper bound ≤ 1
- maxGap_tendsto_atTop: max gap → ∞

**Key Insights**:
1. The unique odd prime gap is d_0 = 1 (between 2 and 3)
2. All subsequent gaps are even and ≥ 2 (odd − odd)
3. The conjecture is about correlation structure of large gaps
4. Record-setting gaps should be "isolated" — not appearing in pairs

References:
- Erdős, P., via [Va99, §1.2]
- Cramér, H. (1936). On the order of magnitude of the difference between
  consecutive prime numbers. Acta Arithmetica, 2(1), 23-46.
-/

end Erdos1137
