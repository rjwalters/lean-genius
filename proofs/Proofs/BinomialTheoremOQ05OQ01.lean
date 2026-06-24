/-
# Chu–Vandermonde Convolution Identities

**Open Question (binomial-theorem-oq-05-oq-01).** The binomial theorem expands
`(x + y)ⁿ = ∑ₖ C(n,k) xᵏ yⁿ⁻ᵏ`. Multiplying two such expansions and comparing
coefficients yields the **Chu–Vandermonde identity** — the fundamental
*convolution* law for binomial coefficients:

  `C(m + n, k) = ∑ᵢ C(m, i) · C(n, k − i)`.

Mathlib proves only the **antidiagonal** form (`Nat.add_choose_eq`), summing over
pairs `(i, j)` with `i + j = k`. This file develops the textbook `range`-indexed
form and two of its most useful specializations, none of which are in Mathlib.

**What this file proves.**
- `chu_vandermonde` — the `range`-form convolution
  `C(m + n, k) = ∑_{i=0}^{k} C(m,i) · C(n, k − i)`, obtained from the antidiagonal
  form by the standard `(i, k − i)` reparametrization.
- `sum_choose_mul_choose_add` — the **diagonal convolution**
  `∑_{k=0}^{n} C(n,k) · C(n, k + d) = C(2n, n + d)`, the off-center Vandermonde
  identity; the surplus terms (`k + d > n`) vanish automatically.
- `sum_sq_choose` — the celebrated **sum of squares of binomial coefficients**
  `∑_{k=0}^{n} C(n,k)² = C(2n, n)`, the central binomial coefficient; the `d = 0`
  case of the diagonal convolution.
- `sum_sq_choose_centralBinom` — the same, phrased with Mathlib's `centralBinom`.
- Numeric witnesses.

All results are fully verified: 0 sorries, 0 axioms (only `propext`,
`Classical.choice`, `Quot.sound`).

The single Mathlib input is `Nat.add_choose_eq` (antidiagonal Vandermonde); the
`range`-form, the diagonal convolution, and the sum-of-squares identity are the
original content.
-/

import Mathlib

open Finset

namespace BinomialTheoremOQ05OQ01

/-- **Chu–Vandermonde identity (range form).** The number of ways to choose `k`
objects from a pile of `m + n` splits, by how many come from the first `m`:
`C(m + n, k) = ∑_{i=0}^{k} C(m, i) · C(n, k − i)`.

Mathlib's `Nat.add_choose_eq` states this over the antidiagonal of `k`; here we
reparametrize each pair `(i, j)` with `i + j = k` as `(i, k − i)`, the form found
in every combinatorics text. -/
theorem chu_vandermonde (m n k : ℕ) :
    (m + n).choose k = ∑ i ∈ range (k + 1), m.choose i * n.choose (k - i) := by
  rw [Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => m.choose a * n.choose b) k]

/-- **Diagonal Vandermonde convolution.** Summing products of binomial
coefficients a fixed distance `d` apart along a row of Pascal's triangle gives a
single off-center central coefficient:
`∑_{k=0}^{n} C(n,k) · C(n, k + d) = C(2n, n + d)`.

This is `chu_vandermonde n n (n + d)` after reflecting `i ↦ n − i` and discarding
the terms with `i > n` (where `C(n, i) = 0`); the surviving index `k = i − d`
runs over the diagonal. -/
theorem sum_choose_mul_choose_add (n d : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * n.choose (k + d) = (2 * n).choose (n + d) := by
  rw [two_mul, chu_vandermonde n n (n + d)]
  -- Goal: ∑_{k<n+1} C(n,k)·C(n,k+d) = ∑_{i<n+d+1} C(n,i)·C(n, (n+d)-i)
  -- The tail i = n+1 … n+d contributes nothing: C(n, i) = 0 there.
  have hsub : range (n + 1) ⊆ range (n + d + 1) :=
    Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
  rw [← Finset.sum_subset hsub
        (fun i _ hi => by
          rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hi
          rw [Nat.choose_eq_zero_of_lt hi, Nat.zero_mul])]
  -- Goal: ∑_{k<n+1} C(n,k)·C(n,k+d) = ∑_{i<n+1} C(n,i)·C(n, (n+d)-i)
  rw [← Finset.sum_range_reflect (fun i => n.choose i * n.choose (n + d - i)) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  have hsub : n + 1 - 1 - i = n - i := by omega
  rw [hsub, Nat.choose_symm hi]
  have hidx : n + d - (n - i) = i + d := by omega
  rw [hidx]

/-- **Sum of squares of binomial coefficients.** A full row of Pascal's triangle,
squared and summed, is the central binomial coefficient:
`∑_{k=0}^{n} C(n,k)² = C(2n, n)`.

This is the `d = 0` case of `sum_choose_mul_choose_add`. Combinatorially: choosing
`n` objects from `2n` by selecting `k` from the first `n` and `n − k` from the
last `n`, with `C(n, n − k) = C(n, k)`. -/
theorem sum_sq_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = (2 * n).choose n := by
  have h := sum_choose_mul_choose_add n 0
  simpa [sq, Nat.add_zero] using h

/-- The sum-of-squares identity phrased with Mathlib's `centralBinom`:
`∑_{k=0}^{n} C(n,k)² = centralBinom n`. -/
theorem sum_sq_choose_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = n.centralBinom := by
  rw [sum_sq_choose, Nat.centralBinom_eq_two_mul_choose]

/-! ### Numeric witnesses -/

/-- Range-form Vandermonde, `m = n = 2`, `k = 2`: `C(4,2) = 6 = 1·1 + 2·2 + 1·1`. -/
example : (2 + 2).choose 2 = ∑ i ∈ range (2 + 1), (2).choose i * (2).choose (2 - i) :=
  chu_vandermonde 2 2 2

/-- Sum of squares, `n = 3`: `1² + 3² + 3² + 1² = 20 = C(6,3)`. -/
example : ∑ k ∈ range (3 + 1), ((3).choose k) ^ 2 = (2 * 3).choose 3 :=
  sum_sq_choose 3

/-- Diagonal convolution, `n = 4`, `d = 1`:
`∑_{k=0}^{4} C(4,k)·C(4,k+1) = C(8,5) = 56`. -/
example : ∑ k ∈ range (4 + 1), (4).choose k * (4).choose (k + 1) = (2 * 4).choose (4 + 1) :=
  sum_choose_mul_choose_add 4 1

/-- Explicit value of the sum of squares for `n = 4`: equals `C(8,4) = 70`. -/
example : ∑ k ∈ range (4 + 1), ((4).choose k) ^ 2 = 70 := by decide

end BinomialTheoremOQ05OQ01
