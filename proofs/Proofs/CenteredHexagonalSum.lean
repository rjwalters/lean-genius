import Mathlib

/-
# Centered Hexagonal Numbers Sum to Cubes

## Open Question (centered-hexagonal-sum-oq-01)

The k-th *centered hexagonal number* is `Hₖ = 3k(k−1)+1` — the count of dots in
`k` nested hexagonal rings: `1, 7, 19, 37, 61, …`.  The classical figurate
identity states that the sum of the first `n` of them is always the perfect
cube `n³`:

    ∑_{k=1}^{n} (3k(k−1)+1) = n³        (1 + 7 + 19 = 27 = 3³).

## Result

A fully machine-checked, self-contained proof, stated in two equivalent forms:

* `sum_centeredHex_range` — the reindexed form `∑_{k<n} H_{k+1} = n³`, whose
  inductive step closes in a single `ring` call (the reindexing `H_{k+1}` removes
  any truncated ℕ subtraction).
* `sum_centeredHex_Icc` — the classical `1`-indexed statement `∑_{k=1}^{n} Hₖ = n³`
  over the interval `[1, n]`, proved by the same one-step induction with
  `Finset.sum_Icc_succ_top`.

The cube-shell intuition is captured by `centeredHex_eq_cube_diff`, the
telescoping identity `Hₖ = k³ − (k−1)³`: each centered hexagonal number is the
gap between consecutive cubes, which is *why* the partial sums collapse to `n³`.

## Novelty

Mathlib has the Gauss triangular-number identity and (via the sister gallery
entry) Nicomachus's `∑k³ = (∑k)²`, but no named "centered hexagonal partial sum
= n³" lemma.  This file supplies it.  The main statement lives entirely in ℕ
(the summand `3k(k−1)+1` is a natural number), so no integer casts are needed
for the headline result; casts appear only in the optional cube-difference
identity, where genuine subtraction occurs.

0 sorries, 0 axioms.
-/

namespace CenteredHexagonalSum

open Finset

/-- The `k`-th **centered hexagonal number** `Hₖ = 3k(k−1)+1`: the sequence
`1, 7, 19, 37, 61, …` (OEIS A003215). -/
def centeredHex (k : ℕ) : ℕ := 3 * k * (k - 1) + 1

/-- Reindexed summand: `H_{k+1} = 3(k+1)k + 1`.  Shifting the index by one turns
the truncated ℕ subtraction `(k+1) − 1` into the honest `k`, so the term is a
plain polynomial that `ring` can manipulate. -/
theorem centeredHex_succ (k : ℕ) : centeredHex (k + 1) = 3 * (k + 1) * k + 1 := by
  simp [centeredHex]

/-- **Cube-shell identity.**  Each centered hexagonal number is the difference of
consecutive cubes, `Hₖ = k³ − (k−1)³`.  Stated over ℤ because the subtraction is
genuine (e.g. `H₀ = 0³ − (−1)³ = 1`).  This is the geometric reason the partial
sums telescope to `n³`: the `n` hexagonal shells are exactly the `n` cubic
shells `k³ − (k−1)³`. -/
theorem centeredHex_eq_cube_diff (k : ℕ) :
    (centeredHex k : ℤ) = (k : ℤ) ^ 3 - ((k : ℤ) - 1) ^ 3 := by
  cases k with
  | zero => norm_num [centeredHex]
  | succ p =>
    simp only [centeredHex, Nat.succ_sub_one]
    push_cast
    ring

/-- **Centered hexagonal sum (reindexed form).**  The first `n` centered
hexagonal numbers sum to `n³`:

`∑_{k<n} H_{k+1} = n³`.

The induction is immediate: peeling the top term with `Finset.sum_range_succ` and
applying the inductive hypothesis leaves `m³ + (3(m+1)m + 1) = (m+1)³`, an
identity `ring` closes outright. -/
theorem sum_centeredHex_range (n : ℕ) :
    ∑ k ∈ range n, centeredHex (k + 1) = n ^ 3 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, centeredHex_succ]
    ring

/-- **Centered hexagonal sum (classical 1-indexed form).**

`∑_{k=1}^{n} Hₖ = n³`.

This is the statement exactly as Nicomachus-style figurate identities are
usually phrased — over the interval `[1, n]`.  It is proved by the same one-step
induction, peeling the top term `H_{m+1}` with `Finset.sum_Icc_succ_top`. -/
theorem sum_centeredHex_Icc (n : ℕ) :
    ∑ k ∈ Icc 1 n, centeredHex k = n ^ 3 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, centeredHex_succ]
    ring

end CenteredHexagonalSum
