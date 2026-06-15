import Mathlib

/-
# Nicomachus's Theorem via the Odd-Number Partition (sum-of-kth-powers OQ-03)

A **second, structurally independent** proof of Nicomachus's identity
  ∑_{i=0}^{n} i³ = (∑_{i=0}^{n} i)²
already proved algebraically in `Proofs/SumOfKthPowers.lean`
(`SumOfKthPowers.sum_cubes_eq_sum_squared`, via the closed forms
`(n(n+1)/2)²`).

Where the parent composes closed forms, this proof uses the classical
**odd-number partition**: the sum of the first `m` odd numbers is `m²`
(`sum_odds`), and the cubes telescope through consecutive square staircases —
the `(n+1)`-th cube is exactly the next block of `n+1` odd numbers,
`(s + (n+1))² − s²` where `s = ∑_{i≤n} i`. Summing the blocks reproduces the
first `T_n = ∑ i` odd numbers, whose total is `T_n² = (∑ i)²`. No closed form
for `∑ i³` is used, so the derivation shares nothing with the parent beyond
the Gauss sum.

The corollary `sum_cubes_eq_sum_first_odds` states the combinatorial identity
literally: `∑ i³ = ∑_{j < ∑ i} (2j+1)` — "the sum of cubes is the sum of the
first `T_n` odd numbers".

Arithmetic independently certified (sympy + brute force, n = 0..60) by
`research/problems/sum-of-kth-powers-oq-03/verify_m1.py`.
-/

open Finset

namespace SumOfKthPowersOQ03

/-- The sum of the first `m` odd numbers is `m²` (the combinatorial core). -/
theorem sum_odds (m : ℕ) : ∑ j ∈ range m, (2 * j + 1) = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- **Nicomachus's theorem**, proved via the odd-number partition.

The induction is the staircase telescope: adding index `n+1` extends the sum
of squares from `s²` to `(s+(n+1))²`, and the increment `(s+(n+1))² − s²`
equals `(n+1)³` because `2·s = (n+1)·n` (Gauss). This is the block-of-odds
identity, independent of the parent's closed-form computation. -/
theorem sum_cubes_eq_sum_squared_via_odds (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 3 = (∑ i ∈ range (n + 1), i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]            -- expand the cube sum (leftmost match)
    conv_rhs => rw [Finset.sum_range_succ]  -- expand the index sum on the RHS only
    rw [ih]
    have hs : (∑ i ∈ range (n + 1), i) * 2 = (n + 1) * n := by
      simpa using Finset.sum_range_id_mul_two (n + 1)
    set s := ∑ i ∈ range (n + 1), i with hsdef
    -- goal: s ^ 2 + (n + 1) ^ 3 = (s + (n + 1)) ^ 2
    have expand : (s + (n + 1)) ^ 2 = s ^ 2 + (n + 1) * (s * 2) + (n + 1) ^ 2 := by
      ring
    rw [expand, hs]
    ring

/-- The combinatorial reading: the sum of cubes equals the sum of the first
`T_n = ∑ i` odd numbers. -/
theorem sum_cubes_eq_sum_first_odds (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 3
      = ∑ j ∈ range (∑ i ∈ range (n + 1), i), (2 * j + 1) := by
  rw [sum_odds, sum_cubes_eq_sum_squared_via_odds]

/-- Numerical sanity check against the algebraic identity. -/
example : ∑ i ∈ range 11, i ^ 3 = (∑ i ∈ range 11, i) ^ 2 := by native_decide

end SumOfKthPowersOQ03
