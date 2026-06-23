import Mathlib

/-
# The Off-Diagonal Vandermonde Convolution

## Open Question OQ-07-OQ-02

The parent entry `combinations-formula-oq-07` reindexes Mathlib's antidiagonal
form of Vandermonde's identity (`Nat.add_choose_eq`) into the single-sum
*range* form

  C(m + n, k) = ∑_{i=0}^{k} C(m, i) · C(n, k - i),

and reads off the celebrated *diagonal* special case

  C(2n, n) = ∑_{i=0}^{n} C(n, i)² .

This follow-up develops the **off-diagonal** companion.  Where the diagonal
identity pairs each entry of row `n` with itself, the off-diagonal identity
slides the second factor by a fixed shift `r`:

  C(m + n, n − r) = ∑_{i=0}^{n−r} C(m, i) · C(n, i + r)        (r ≤ n).

The diagonal sum-of-squares is precisely the central case `m = n`, `r = 0`, so
this identity is a genuine two-parameter generalisation of the parent's
headline rather than a restatement of it.

## Why the shift is natural

Setting `r = 0` and replacing `C(n, i)` by `C(n, n − i)` (symmetry) turns the
range form of Vandermonde at `k = n` into the *mixed* product sum

  C(m + n, n) = ∑_{i=0}^{n} C(m, i) · C(n, i) ,

an identity from Gould's combinatorial tables.  Carrying a shift `r` through the
same computation — and choosing the summation range so that **every** term
stays inside the symmetry window `i + r ≤ n` — yields the off-diagonal form
above with no vanishing tail to discard.  This is the cleanest route: it never
needs to split the sum into nonzero and zero parts.

## Results

* `add_choose_eq_sum_range` — the range form of Vandermonde (re-derived here so
  the file is self-contained).
* `sum_choose_mul_choose_shift` — the off-diagonal convolution
  `C(m + n, n − r) = ∑_{i=0}^{n−r} C(m, i) · C(n, i + r)`.
* `sum_choose_mul_choose` — the `r = 0` mixed product sum
  `C(m + n, n) = ∑_{i=0}^{n} C(m, i) · C(n, i)`.
* `central_sum_sq_shift` — the `m = n` central case
  `C(2n, n − r) = ∑_{i=0}^{n−r} C(n, i) · C(n, i + r)`.
* `central_binom_eq_sum_sq` — recovers the parent's diagonal
  `C(2n, n) = ∑_{i=0}^{n} C(n, i)²` as the `m = n`, `r = 0` corner.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ02

open Finset

/-- **Vandermonde's convolution (range form).**
    `C(m + n, k) = ∑_{i=0}^{k} C(m, i) · C(n, k - i)`.  This is `Nat.add_choose_eq`
    pushed through `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`. -/
theorem add_choose_eq_sum_range (m n k : ℕ) :
    (m + n).choose k = ∑ i ∈ Finset.range (k + 1), m.choose i * n.choose (k - i) := by
  rw [Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => m.choose i * n.choose j) k]

/-- **Off-diagonal Vandermonde convolution.**
    For a shift `r ≤ n`,
        `C(m + n, n − r) = ∑_{i=0}^{n−r} C(m, i) · C(n, i + r)`.
    The summation range `i ≤ n − r` guarantees `i + r ≤ n`, so the symmetry
    `C(n, (n−r) − i) = C(n, i + r)` applies to every term. -/
theorem sum_choose_mul_choose_shift (m n r : ℕ) (hr : r ≤ n) :
    (m + n).choose (n - r) = ∑ i ∈ Finset.range (n - r + 1), m.choose i * n.choose (i + r) := by
  rw [add_choose_eq_sum_range]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  -- `i ≤ n - r` and `r ≤ n` give `i + r ≤ n`, and `(n - r) - i = n - (i + r)`.
  have hsub : n - r - i = n - (i + r) := by omega
  rw [hsub, Nat.choose_symm (by omega)]

/-- **Mixed product sum** (`r = 0`).
    `C(m + n, n) = ∑_{i=0}^{n} C(m, i) · C(n, i)`. -/
theorem sum_choose_mul_choose (m n : ℕ) :
    (m + n).choose n = ∑ i ∈ Finset.range (n + 1), m.choose i * n.choose i := by
  have h := sum_choose_mul_choose_shift m n 0 (Nat.zero_le n)
  simpa using h

/-- **Central off-diagonal case** (`m = n`).
    `C(2n, n − r) = ∑_{i=0}^{n−r} C(n, i) · C(n, i + r)` for `r ≤ n`. -/
theorem central_sum_sq_shift (n r : ℕ) (hr : r ≤ n) :
    (2 * n).choose (n - r) = ∑ i ∈ Finset.range (n - r + 1), n.choose i * n.choose (i + r) := by
  rw [two_mul]
  exact sum_choose_mul_choose_shift n n r hr

/-- **Parent's diagonal identity recovered** (`m = n`, `r = 0`).
    `C(2n, n) = ∑_{i=0}^{n} C(n, i)²` — the central case of the off-diagonal
    convolution.  Matches `CombinationsFormulaOQ07.central_binom_eq_sum_sq`. -/
theorem central_binom_eq_sum_sq (n : ℕ) :
    (2 * n).choose n = ∑ i ∈ Finset.range (n + 1), (n.choose i) ^ 2 := by
  have h := central_sum_sq_shift n 0 (Nat.zero_le n)
  simp only [Nat.sub_zero, Nat.add_zero] at h
  rw [h]
  exact Finset.sum_congr rfl (fun i _ => (sq (n.choose i)).symm)

/-- Sanity check: `C(5, 1) = 5` from the shift `r = 1` with `m = 2`, `n = 3`:
    `∑_{i=0}^{2} C(2,i)·C(3,i+1) = 1·3 + 2·3 + 1·1 = 10`. -/
example : (2 + 3).choose (3 - 1) = 10 := by
  rw [sum_choose_mul_choose_shift 2 3 1 (by norm_num)]
  decide

/-- Sanity check: the diagonal `C(6, 3) = 20 = 1 + 9 + 9 + 1`. -/
example : (2 * 3).choose 3 = 20 := by
  rw [central_binom_eq_sum_sq 3]
  decide

end CombinationsFormulaOQ07OQ02
