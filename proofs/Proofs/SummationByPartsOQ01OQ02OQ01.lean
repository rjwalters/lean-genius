import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-
# Second-moment sum `∑ k²·rᵏ` over any field: falling factorials and Abel summation

## What This Proves

For a field element `r ≠ 1` and a natural number `n`,

    ∑_{k=0}^{n-1} k² · rᵏ
      = (rⁿ·(n² + (1 + 2n − 2n²)·r + (n−1)²·r²) − r − r²) / (r − 1)³.

This is the **second-moment** arithmetico-geometric sum (each term `k²` times a
geometric factor `rᵏ`).  Dropping the `rⁿ`-block leaves `(−r − r²)/(r − 1)³ =
r(1+r)/(1−r)³`, the classical `∑ k²·rᵏ` for `|r| < 1`.

## Relation to the Sibling Entry

The entry `summation-by-parts-oq-01-oq-02` establishes the same headline closed
form, but only **over `ℝ`** and **by bare induction** (clearing `(1−r)³` and
closing with `ring`).  This entry strengthens that result along three axes:

* **Generality.** The identity holds over an *arbitrary field* `K`, with no
  reference to `ℝ` — it is an algebraic, not analytic, fact.
* **The genuine summation-by-parts derivation.** The sibling never actually uses
  Abel summation (despite the entry-family name).  Here
  `sum_range_sq_geom_eq_byParts` re-derives the sum through
  `Finset.sum_range_by_parts`, exposing that the weight `f(k) = k²` has *linear*
  forward differences `f(k+1) − f k = 2k + 1`, so each nested geometric partial
  sum is weighted by `2i + 1` — the discrete signature of differentiating `k²`.
* **The falling-factorial companion and decomposition.**
  `sum_range_falling_geom` evaluates `∑ k(k−1)·rᵏ` (the discrete second
  derivative of the geometric series, limit `2r²/(1−r)³`), and
  `sum_sq_eq_falling_add_linear` realizes `k² = k(k−1) + k` as a term-by-term
  identity of finite sums — tying the second moment, the second falling moment,
  and the first moment into one family.

## Method

Both closed forms are proved by induction on `n`: `Finset.sum_range_succ` adds
the next term to the closed form at `m`, and clearing the common denominator
`(r−1)³` (using `r − 1 ≠ 0`) reduces the goal to a polynomial identity closed by
`ring` after `push_cast`/`field_simp`.  The decomposition is `Finset.sum_add_distrib`
plus `ring` on the summand; the Abel form specializes `Finset.sum_range_by_parts`.
-/

namespace SummationByPartsOQ01OQ02OQ01

open Finset

variable {K : Type*} [Field K]

/-- **Second-moment arithmetico-geometric sum, closed form, over any field.**
For `r ≠ 1`,
`∑_{k<n} k²·rᵏ = (rⁿ·(n² + (1 + 2n − 2n²)·r + (n−1)²·r²) − r − r²)/(r−1)³`. -/
theorem sum_range_sq_geom {r : K} (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, (k : K) ^ 2 * r ^ k
      = (r ^ n * ((n : K) ^ 2 + (1 + 2 * (n : K) - 2 * (n : K) ^ 2) * r
            + ((n : K) - 1) ^ 2 * r ^ 2) - r - r ^ 2) / (r - 1) ^ 3 := by
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

/-- **Second falling-factorial sum, closed form.**
For `r ≠ 1`,
`∑_{k<n} k(k−1)·rᵏ = (rⁿ·(n(n−1) + (4n − 2n²)·r + (n−1)(n−2)·r²) − 2r²)/(r−1)³`.
This is the discrete analogue of the second derivative of the geometric series;
its `n → ∞` limit for `|r| < 1` is `2r²/(1−r)³`. -/
theorem sum_range_falling_geom {r : K} (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, (k : K) * ((k : K) - 1) * r ^ k
      = (r ^ n * ((n : K) * ((n : K) - 1) + (4 * (n : K) - 2 * (n : K) ^ 2) * r
            + ((n : K) - 1) * ((n : K) - 2) * r ^ 2) - 2 * r ^ 2) / (r - 1) ^ 3 := by
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

/-- **Structural decomposition `k² = k(k−1) + k`.**
The second moment splits, term by term, as the second falling moment plus the
first moment — no closed forms required. -/
theorem sum_sq_eq_falling_add_linear (r : K) (n : ℕ) :
    ∑ k ∈ range n, (k : K) ^ 2 * r ^ k
      = (∑ k ∈ range n, (k : K) * ((k : K) - 1) * r ^ k)
        + ∑ k ∈ range n, (k : K) * r ^ k := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The second-moment sum re-derived through **Abel's summation by parts**.
Taking the weight `f k = (k : K)²` and the geometric sequence `g k = rᵏ`,
`Finset.sum_range_by_parts` rewrites the sum as a boundary term minus a
correction whose increments `f(k+1) − f k = 2k + 1` are *linear* in `k`; the
correction therefore weights each nested geometric partial sum by `2i + 1`. -/
theorem sum_range_sq_geom_eq_byParts (r : K) (n : ℕ) :
    ∑ k ∈ range n, (k : K) ^ 2 * r ^ k
      = (↑(n - 1) : K) ^ 2 * (∑ i ∈ range n, r ^ i)
        - ∑ i ∈ range (n - 1), (2 * (i : K) + 1) * (∑ j ∈ range (i + 1), r ^ j) := by
  have h := Finset.sum_range_by_parts (fun k => (k : K) ^ 2) (fun k => r ^ k) n
  simp only [smul_eq_mul] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

end SummationByPartsOQ01OQ02OQ01
