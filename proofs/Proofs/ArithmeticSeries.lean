import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Sum of an Arithmetic Series

## What This Proves
We prove Gauss's formula for the sum of the first n natural numbers and generalize
to arbitrary arithmetic progressions. This is Wiedijk's 100 Theorems #68.

## Historical Context
The formula for 1 + 2 + ... + n = n(n+1)/2 is attributed to Carl Friedrich Gauss,
who allegedly discovered it as a schoolboy. When his teacher asked the class to
sum the numbers 1 to 100 (hoping for a quiet classroom), young Gauss immediately
answered 5050. He had noticed that pairing 1+100, 2+99, 3+98, ... gives 50 pairs
of 101, yielding 50 × 101 = 5050.

While this anecdote may be apocryphal, the formula was known to the ancient Greeks
and appears in works by Archimedes and in Babylonian mathematics.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `Finset.sum_range_id` which proves
  ∑ i in range n, i = n * (n - 1) / 2 (for 0..n-1).
- **Original Contributions:** We derive the classical 1..n formula and the general
  arithmetic series formula. We provide intuitive formulations and the famous
  pairing argument as a teaching example.
- **Proof Techniques Demonstrated:** Bijective summation arguments, algebraic
  manipulation, and connecting to Mathlib's standard forms.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Finset.sum_range_id` : Sum of 0..n-1 equals n*(n-1)/2
- `Finset.sum_range_id_mul_two` : Related identity for Gauss pairing
- `Finset.range` : The set {0, 1, ..., n-1}

Original formalization for Lean Genius.
-/

namespace ArithmeticSeries

open Finset BigOperators

/-! ## The Gauss Summation Formula -/

/-- **Gauss's Formula (0-indexed version from Mathlib)**

    The sum 0 + 1 + 2 + ... + (n-1) = n*(n-1)/2.

    This is the Mathlib convention using `range n` = {0, 1, ..., n-1}. -/
theorem gauss_sum_zero_indexed (n : ℕ) : ∑ i ∈ range n, i = n * (n - 1) / 2 :=
  Finset.sum_range_id n

/-- **Gauss's Formula (classical 1-indexed version)**

    The sum 0 + 1 + 2 + 3 + ... + n = n*(n+1)/2.

    This is the formula young Gauss allegedly used to sum 1 to 100.
    Using range (n+1) gives us {0, 1, ..., n}. -/
theorem gauss_sum (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  have h := Finset.sum_range_id (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [Nat.mul_comm] at h
  exact h

/-! ## The Pairing Argument (Gauss's Method)

The key insight is that we can pair terms from opposite ends of the sequence.
If S = 1 + 2 + ... + n, then writing S twice (forwards and backwards):

    S = 1   +   2   +   3   + ... + (n-1) +   n
    S = n   + (n-1) + (n-2) + ... +   2   +   1
   ──────────────────────────────────────────────
   2S = (n+1) + (n+1) + (n+1) + ... + (n+1) + (n+1)
      = n × (n+1)

Therefore S = n(n+1)/2.
-/

/-- The pairing identity: 2 × sum(0..n) = n × (n+1)

    This is the algebraic heart of Gauss's pairing argument. -/
theorem pairing_identity_mul_two (n : ℕ) :
    (∑ i ∈ range (n + 1), i) * 2 = n * (n + 1) := by
  have h := Finset.sum_range_id_mul_two (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [Nat.mul_comm (n + 1) n] at h
  exact h

/-! ## General Arithmetic Series -/

/-- **Sum of an Arithmetic Series**

    For an arithmetic progression with first term a, common difference d, and n terms:
    ∑_{k=0}^{n-1} (a + k*d) = n*a + d*n*(n-1)/2

    This generalizes Gauss's formula where a=0, d=1 gives us ∑_{k=0}^{n-1} k. -/
theorem arithmetic_series_sum (a d n : ℕ) :
    ∑ k ∈ range n, (a + k * d) = n * a + d * (n * (n - 1) / 2) := by
  rw [sum_add_distrib, sum_const, card_range]
  simp only [Nat.nsmul_eq_mul]
  rw [mul_comm d, ← sum_mul, sum_range_id]

/-! ## Famous Special Cases -/

/-- Sum of first 100 natural numbers (Gauss's original problem) -/
theorem gauss_100 : ∑ i ∈ range 101, i = 5050 := by native_decide

/-- Sum of first 10 natural numbers: 0 + 1 + 2 + ... + 10 = 55 -/
theorem sum_0_to_10 : ∑ i ∈ range 11, i = 55 := by native_decide

/-- Sum of odd numbers: 1 + 3 + 5 + ... + (2n-1) = n²

    This beautiful identity shows that the n-th square is the sum of the
    first n odd numbers. It has a lovely visual proof: each odd number
    adds an "L-shaped" layer to a growing square. -/
theorem sum_odd_numbers (n : ℕ) : ∑ k ∈ range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

/-- Sum of even numbers: 0 + 2 + 4 + ... + 2(n-1) = n*(n-1)

    Using the arithmetic series with a=0 and d=2. -/
theorem sum_even_numbers (n : ℕ) : ∑ k ∈ range n, (2 * k) = n * (n - 1) := by
  have h : ∑ k ∈ range n, (2 * k) = (∑ k ∈ range n, k) * 2 := by
    rw [sum_mul]
    congr 1
    ext k
    ring
  rw [h, sum_range_id_mul_two]

/-! ## Triangular Numbers -/

/-- The n-th triangular number is the sum 0 + 1 + 2 + ... + n -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The sum formula gives triangular numbers -/
theorem sum_eq_triangular (n : ℕ) : ∑ i ∈ range (n + 1), i = triangular n := by
  rw [triangular, gauss_sum]

/-- Triangular numbers satisfy the recurrence T(n+1) = T(n) + (n+1) -/
theorem triangular_recurrence (n : ℕ) :
    triangular (n + 1) = triangular n + (n + 1) := by
  simp only [triangular]
  -- (n+1)(n+2)/2 = n(n+1)/2 + (n+1)
  -- We use a direct calculation approach
  have hdiv : 2 ∣ n * (n + 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk]; use k * (2 * k + 1); ring
    · rw [hk]; use (2 * k + 1) * (k + 1); ring
  -- Rewrite n * (n + 1) as 2 * k for some k
  obtain ⟨m, hm⟩ := hdiv
  calc (n + 1) * (n + 1 + 1) / 2
      = (n + 1) * (n + 2) / 2 := by ring_nf
    _ = (n * (n + 1) + 2 * (n + 1)) / 2 := by ring_nf
    _ = (2 * m + 2 * (n + 1)) / 2 := by rw [hm]
    _ = m + (n + 1) := by omega
    _ = n * (n + 1) / 2 + (n + 1) := by rw [hm]; simp [Nat.mul_div_cancel_left]

/-- Twice a triangular number -/
theorem triangular_mul_two (n : ℕ) : triangular n * 2 = n * (n + 1) := by
  simp only [triangular]
  rw [Nat.div_mul_cancel]
  -- 2 divides n*(n+1) because one of n, n+1 is even
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]
    exact ⟨k * (2 * k + 1), by ring⟩
  · rw [hk]
    exact ⟨(2 * k + 1) * (k + 1), by ring⟩

#check gauss_sum
#check gauss_sum_zero_indexed
#check arithmetic_series_sum
#check sum_odd_numbers
#check triangular
#check triangular_recurrence

end ArithmeticSeries
