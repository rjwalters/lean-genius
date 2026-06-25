import Mathlib

/-
# Sum of Cubes of the First n Odd Numbers

## Open Question (odd-cubes-sum-oq-01)

The odd-indexed companion of Nicomachus's `∑k³ = (∑k)²`.  Summing the cubes of
the first `n` odd numbers gives the closed form `n²(2n²−1)`:

    ∑_{k=1}^{n} (2k−1)³ = n²(2n²−1)        (1 + 27 + 125 = 153 = 3²·17).

The first few partial sums are `1, 28, 153, 496, 1225, …` (OEIS A002593).

## Result

A fully machine-checked, self-contained proof, organised around a single
subtraction-free core identity:

* `sum_oddCube_add` — the headline result in its *subtraction-free* form
  `(∑_{k<n} (2k+1)³) + n² = 2n⁴`.  Both sides are honest ℕ polynomials, so the
  induction never leaves ℕ: the inductive step closes by `ring` (on a pure
  polynomial identity) glued together with `omega`.

* `sum_oddCube_range` — the named closed form `∑_{k<n} (2k+1)³ = n²(2n²−1)`,
  derived from the additive core.  The closed form `n²(2n²−1) = 2n⁴ − n²`
  carries a genuine subtraction, handled once via `Nat.sub_add_cancel`.

* `sum_oddCube_Icc` — the classical `1`-indexed statement
  `∑_{k=1}^{n} (2k−1)³ = n²(2n²−1)` over the interval `[1, n]`, obtained by
  reindexing the range form.

The telescoping intuition is captured by `oddCube_telescope`, the difference
identity `(2n−1)³ = f(n) − f(n−1)` with `f(n) = n²(2n²−1)`: each odd cube is the
gap between consecutive values of the closed form, which is *why* the partial
sums collapse to `n²(2n²−1)`.

## Novelty

Mathlib has Nicomachus's `∑k³ = (∑k)²` (via the sister gallery entry) and the
Gauss/​square-pyramidal power sums, but no named "sum of cubes of odd numbers"
identity.  This file supplies it.  The headline is stated in the genuinely
subtraction-free form `(∑(2k+1)³) + n² = 2n⁴`, so the core induction stays
entirely inside ℕ; subtraction appears only when packaging the conventional
closed form `n²(2n²−1)` and in the optional telescoping identity over ℤ.

0 sorries, 0 axioms.
-/

namespace OddCubesSum

open Finset

/-- The cube of the `k`-th **odd number**, `(2k−1)³`: the sequence
`1, 27, 125, 343, …` for `k = 1, 2, 3, 4`.  (At `k = 0` the truncated ℕ
subtraction gives `(2·0−1)³ = 0`, but every sum below indexes from `k ≥ 1`.) -/
def oddCube (k : ℕ) : ℕ := (2 * k - 1) ^ 3

/-- Reindexed summand: `oddCube (k+1) = (2k+1)³`.  Shifting the index by one
turns the truncated ℕ subtraction `2(k+1)−1` into the honest `2k+1`, so the term
is a plain polynomial that `ring` can manipulate. -/
theorem oddCube_succ (k : ℕ) : oddCube (k + 1) = (2 * k + 1) ^ 3 := by
  have h : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [oddCube, h]

/-- **Telescoping identity.**  With closed form `f(n) = n²(2n²−1)`, each odd cube
is the difference of consecutive values, `(2n−1)³ = f(n) − f(n−1)`.  Stated over
ℤ because the subtraction is genuine.  This is the reason the partial sums
telescope to `n²(2n²−1)`: the `n` odd cubes are exactly the `n` increments of
`f`. -/
theorem oddCube_telescope (n : ℤ) :
    (2 * n - 1) ^ 3 = n ^ 2 * (2 * n ^ 2 - 1) - (n - 1) ^ 2 * (2 * (n - 1) ^ 2 - 1) := by
  ring

/-- **Sum of odd cubes (subtraction-free core).**  The cubes of the first `n` odd
numbers, reindexed from `0`, satisfy

`(∑_{k<n} (2k+1)³) + n² = 2n⁴`.

Both sides are honest ℕ polynomials — no truncated subtraction anywhere — so the
induction stays inside ℕ.  The step peels the top term with
`Finset.sum_range_succ`; the polynomial identity
`2m⁴ + (2m+1)³ + (m+1)² = 2(m+1)⁴ + m²` (closed by `ring`) plus the inductive
hypothesis are then combined by `omega`. -/
theorem sum_oddCube_add (n : ℕ) :
    (∑ k ∈ range n, oddCube (k + 1)) + n ^ 2 = 2 * n ^ 4 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, oddCube_succ]
    have expand : 2 * m ^ 4 + (2 * m + 1) ^ 3 + (m + 1) ^ 2
        = 2 * (m + 1) ^ 4 + m ^ 2 := by ring
    omega

/-- **Closed-form bridge.**  The conventional closed form `n²(2n²−1)` satisfies
the same additive relation as the sum, `n²(2n²−1) + n² = 2n⁴`.  The form
`n²(2n²−1) = 2n⁴ − n²` carries a genuine ℕ subtraction, resolved once via
`Nat.sub_add_cancel` (using `1 ≤ 2n²` for `n ≥ 1`). -/
theorem closedForm_add (n : ℕ) : n ^ 2 * (2 * n ^ 2 - 1) + n ^ 2 = 2 * n ^ 4 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hx : 0 < n ^ 2 := pow_pos h 2
    have h1 : 1 ≤ 2 * n ^ 2 := by omega
    calc n ^ 2 * (2 * n ^ 2 - 1) + n ^ 2
        = n ^ 2 * (2 * n ^ 2 - 1) + n ^ 2 * 1 := by ring
      _ = n ^ 2 * ((2 * n ^ 2 - 1) + 1) := by rw [← Nat.mul_add]
      _ = n ^ 2 * (2 * n ^ 2) := by rw [Nat.sub_add_cancel h1]
      _ = 2 * n ^ 4 := by ring

/-- **Sum of odd cubes (reindexed range form).**

`∑_{k<n} (2k+1)³ = n²(2n²−1)`.

Both the sum and the closed form satisfy the same additive identity
(`sum_oddCube_add` and `closedForm_add`, each equal to `2n⁴` after adding `n²`),
so `omega` identifies them. -/
theorem sum_oddCube_range (n : ℕ) :
    ∑ k ∈ range n, oddCube (k + 1) = n ^ 2 * (2 * n ^ 2 - 1) := by
  have hadd := sum_oddCube_add n
  have hmul := closedForm_add n
  omega

/-- **Sum of odd cubes (classical 1-indexed form).**

`∑_{k=1}^{n} (2k−1)³ = n²(2n²−1)`.

This is the statement exactly as power-sum identities are usually phrased — over
the interval `[1, n]`.  Proved by the same subtraction-free induction as the
range form: the step peels the top term `oddCube (m+1)` with
`Finset.sum_Icc_succ_top` and closes via the `ring` identity plus `omega`; the
closed form is then matched with `closedForm_add`. -/
theorem sum_oddCube_Icc (n : ℕ) :
    ∑ k ∈ Icc 1 n, oddCube k = n ^ 2 * (2 * n ^ 2 - 1) := by
  have hadd : (∑ k ∈ Icc 1 n, oddCube k) + n ^ 2 = 2 * n ^ 4 := by
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), oddCube_succ]
      have expand : 2 * m ^ 4 + (2 * m + 1) ^ 3 + (m + 1) ^ 2
          = 2 * (m + 1) ^ 4 + m ^ 2 := by ring
      omega
  have hmul := closedForm_add n
  omega

end OddCubesSum
