/-
# Sum of k-th Powers — OQ-03: Nicomachus via the odd-number partition of cubes

Second, structurally independent proof of Nicomachus's theorem

  ∑_{i=0}^{n} i³ = (∑_{i=0}^{n} i)²

The parent `SumOfKthPowers.lean` proves this **algebraically** (`sum_cubes_eq_sum_squared`,
composing the closed forms `sum_cubes_classical` and `sum_first_powers_classical`). This file
gives the classical **combinatorial** proof via the odd-number tiling, sharing no lemma with the
parent beyond the Gauss sum.

## The combinatorial idea

Let `T n = ∑_{i<n} i` be the running Gauss sum (so `T 0 = 0`, `T (i+1) = T i + i`). The cube `i³`
is the sum of the `i` consecutive odd numbers occupying *positions* `T i, T i + 1, …, T (i+1) − 1`
in the sequence of all odds `1, 3, 5, …`:

  ∑_{T i ≤ j < T (i+1)} (2j+1) = i³.

The position blocks `[T i, T (i+1))` for `i = 0..n` tile `[0, T (n+1))` exactly, and the sum of
the first `m` odds is `m²`, so

  ∑_{i ≤ n} i³ = ∑_{j < T (n+1)} (2j+1) = (T (n+1))² = (∑_{i ≤ n} i)².

## Why `T` is a *sum*, not the closed form

Defining `T n` as the Gauss sum (rather than the closed form `n(n+1)/2`) sidesteps **all**
ℕ-division and ℕ-subtraction. The whole proof uses only `ring` (valid on the ℕ semiring),
`Finset.sum_range_succ`, `Finset.sum_Ico_consecutive`, `Finset.range_eq_Ico`, and one
`Nat.add_left_cancel`. The triangular recurrence appears in the division- and subtraction-free
form `2·T i + i = i²` (`two_T_add`), proved by a one-line induction.

## Contents

* `T`, `T_zero`, `T_succ`, `T_le_succ` — the Gauss-sum position function and its recurrence
* `sum_odds`     — L1: `∑_{j<m} (2j+1) = m²`
* `two_T_add`    — `2·T i + i = i²` (division-free triangular recurrence)
* `block_sq`     — `T i² + i³ = T (i+1)²` (each block contributes a cube)
* `block_eq_cube`— L2: `∑_{T i ≤ j < T (i+1)} (2j+1) = i³`
* `tiling`       — L3: blocks tile the first `T n` odds
* `sum_cubes_eq_sum_squared_via_odds` — Nicomachus, matching the parent's RHS shape
* `cube_eq_sum_consecutive_odds` — corollary: `i³` is a sum of `i` consecutive odd numbers

Axioms: 0. Sorries: 0.

NOTE (build provenance): BUILD-PENDING — authored during a Docker + Aristotle backend outage and
NOT yet machine-checked. Registered in `proofs/Proofs.lean`; the two load-bearing Mathlib lemmas
(`Finset.sum_Ico_consecutive`, `Finset.range_eq_Ico`) were pin-confirmed at Lean `v4.26.0`
(Mathlib pin `2df2f01`). Every arithmetic identity is additionally certified (sympy + brute force,
n = 0..60) by `research/problems/sum-of-kth-powers-oq-03/verify_m1.py`. Promote this note (and the
meta.json status to verified/original) once a green `./proofs/scripts/docker-build.sh
Proofs.SumOfKthPowersOQ03` confirms the typecheck.
-/

import Mathlib

open Finset

namespace SumOfKthPowersOQ03

/-- Partial Gauss sum `T n = 0 + 1 + … + (n−1)`: the running count of odd-number positions
consumed by the cubes `0³, 1³, …, (n−1)³`. Defined as a sum (no division). -/
def T (n : ℕ) : ℕ := ∑ i ∈ range n, i

@[simp] theorem T_zero : T 0 = 0 := rfl

/-- Triangular recurrence: `T (n+1) = T n + n`. -/
theorem T_succ (n : ℕ) : T (n + 1) = T n + n := by
  simp [T, Finset.sum_range_succ]

/-- `T` is monotone in one step (the position blocks are non-overlapping). -/
theorem T_le_succ (n : ℕ) : T n ≤ T (n + 1) := by
  rw [T_succ]; exact Nat.le_add_right _ _

/-- **L1 — sum of the first `m` odd numbers is `m²`.** -/
theorem sum_odds (m : ℕ) : ∑ j ∈ range m, (2 * j + 1) = m ^ 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- The Gauss-sum form of the triangular recurrence: `2·T i + i = i²`
(division-free, subtraction-free). -/
theorem two_T_add (i : ℕ) : 2 * T i + i = i ^ 2 := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [T_succ]
    have h : 2 * (T k + k) + (k + 1) = (2 * T k + k) + (2 * k + 1) := by ring
    rw [h, ih]; ring

/-- **Block-square identity:** `T i² + i³ = T (i+1)²`. The odd block at positions
`[T i, T (i+1))` contributes exactly `i³`. Proved from `two_T_add`, all over the ℕ semiring. -/
theorem block_sq (i : ℕ) : T i ^ 2 + i ^ 3 = T (i + 1) ^ 2 := by
  rw [T_succ]
  have h := two_T_add i
  calc T i ^ 2 + i ^ 3
      = T i ^ 2 + i ^ 2 * i := by ring
    _ = T i ^ 2 + (2 * T i + i) * i := by rw [← h]
    _ = (T i + i) ^ 2 := by ring

/-- **L2 — the `i`-th odd block sums to `i³`:** `∑_{T i ≤ j < T (i+1)} (2j+1) = i³`. -/
theorem block_eq_cube (i : ℕ) :
    ∑ j ∈ Ico (T i) (T (i + 1)), (2 * j + 1) = i ^ 3 := by
  have hsplit :
      (∑ j ∈ range (T i), (2 * j + 1))
          + (∑ j ∈ Ico (T i) (T (i + 1)), (2 * j + 1))
        = ∑ j ∈ range (T (i + 1)), (2 * j + 1) := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (T_le_succ i)
  rw [sum_odds, sum_odds] at hsplit
  -- hsplit : T i ^ 2 + block = T (i+1) ^ 2
  have hb := block_sq i  -- T i ^ 2 + i ^ 3 = T (i+1) ^ 2
  have hcancel :
      T i ^ 2 + (∑ j ∈ Ico (T i) (T (i + 1)), (2 * j + 1)) = T i ^ 2 + i ^ 3 := by
    rw [hsplit, hb]
  exact Nat.add_left_cancel hcancel

/-- **L3 — the blocks tile the first `T n` odds:**
`∑_{i<n} (block i) = ∑_{j < T n} (2j+1)`. -/
theorem tiling (n : ℕ) :
    ∑ i ∈ range n, (∑ j ∈ Ico (T i) (T (i + 1)), (2 * j + 1))
      = ∑ j ∈ range (T n), (2 * j + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (T_le_succ k)

/-- **Nicomachus's theorem via the odd-number partition.**

`∑_{i ≤ n} i³ = (∑_{i ≤ n} i)²`, matching the parent's `sum_cubes_eq_sum_squared` exactly, but
proved by the odd-block tiling (L1 + L2 + L3) instead of closed-form polynomials. The final `rfl`
holds because `T (n+1)` is *definitionally* `∑ i ∈ range (n+1), i`. -/
theorem sum_cubes_eq_sum_squared_via_odds (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 3 = (∑ i ∈ range (n + 1), i) ^ 2 := by
  have key : ∑ i ∈ range (n + 1), i ^ 3
      = ∑ i ∈ range (n + 1), (∑ j ∈ Ico (T i) (T (i + 1)), (2 * j + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [block_eq_cube]
  rw [key, tiling (n + 1), sum_odds]
  rfl

/-- **Each cube is a sum of consecutive odd numbers (Nicomachus).**

`i³` equals the sum of the `i` consecutive odd numbers starting at `2·(T i) + 1` — i.e. the odds
occupying positions `T i, …, T(i+1)−1` in the sequence `1, 3, 5, …`. This is the per-cube
decomposition that `block_eq_cube` captures over `Ico (T i) (T (i+1))`, restated as a standalone
identity over `range i` (no ℕ-subtraction: the first odd is `2·T i + 1`). Examples:
`1³ = 1`, `2³ = 3 + 5`, `3³ = 7 + 9 + 11`, `4³ = 13 + 15 + 17 + 19`. -/
theorem cube_eq_sum_consecutive_odds (i : ℕ) :
    i ^ 3 = ∑ k ∈ range i, (2 * (T i + k) + 1) := by
  have h := block_eq_cube i
  rw [Finset.sum_Ico_eq_sum_range, T_succ, Nat.add_sub_cancel_left] at h
  exact h.symm

end SumOfKthPowersOQ03
