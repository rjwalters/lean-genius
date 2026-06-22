import Mathlib
import Proofs.CombinationsFormulaOQ07
import Proofs.CombinationsFormulaOQ07OQ01
import Proofs.CombinationsFormulaOQ07OQ03

/-
# The Cubically Weighted Sum of Squares of Binomial Coefficients

## Open Question OQ-07-OQ-06

The OQ-07 lineage studies the moments of the symmetric distribution
`C(n, k)² / C(2n, n)` on `{0, …, n}`:

  * zeroth moment (parent OQ-07):   `∑_{k} C(n, k)²       = C(2n, n)`,
  * first  moment (OQ-07-OQ-03):    `2 · ∑_{k} k · C(n,k)² = n · C(2n, n)`,
  * second moment (OQ-07-OQ-04):    `∑_{k} k² · C(n,k)²    = n² · C(2n−2, n−1)`.

This file computes the **third moment**:

  2 · ∑_{k=0}^{n} k³ · C(n, k)² = n² · (n + 1) · C(2n − 2, n − 1),         (★)

equivalently in subtraction-free form, writing `n = m + 1`,

  2 · ∑_{k=0}^{m+1} k³ · C(m+1, k)² = (m+1)² · (m+2) · C(2m, m).

Mathlib provides the zeroth-moment row sum (`Nat.sum_range_choose`) but **none**
of the squared-coefficient moments, so (★) is a genuine gap.

## The proof — absorption then first-moment reduction

The engine is the absorption identity (OQ-07-OQ-01, `mul_choose_eq`)

  k · C(n, k) = n · C(n − 1, k − 1).

Squaring it turns a `k²`-weighted square of `C(n, ·)` into an *unweighted* square
of `C(n−1, ·)` one order down; the leftover factor of `k` becomes a `(k+1)` after
the index shift `k ↦ k+1` (which also discards the vanishing `k = 0` term):

  ∑_{k} k³ C(n,k)² = n² ∑_{j} (j+1) C(n−1, j)²
                   = n² ( ∑_{j} j·C(n−1,j)²  +  ∑_{j} C(n−1,j)² ).

The two surviving sums are exactly the **first moment** (OQ-07-OQ-03) and the
**zeroth moment** (parent OQ-07) at level `n − 1`:

  2 ∑_{j} j·C(n−1,j)² = (n−1)·C(2n−2, n−1),     ∑_{j} C(n−1,j)² = C(2n−2, n−1).

Substituting and clearing the `2` gives `(n−1 + 2)·C(2n−2,n−1) = (n+1)·C(2n−2,n−1)`
inside the `n²` factor, which is (★).  No induction or generating functions are
needed — only one absorption step and the two lower moments already in the gallery.

## Mathematical context

Reading `C(n,k)² / C(2n,n)` as the hypergeometric distribution, (★) records its
third raw moment.  Combined with `C(2n,n) = (2(2n−1)/n)·C(2n−2,n−1)`, it yields the
closed form `E[k³] = n³(n+1) / (4(2n−1))` (e.g. `n = 2` gives `E[k³] = 2`).

## Results

1. `sum_cube_weighted_sq_reduce` — the absorption + index-shift step
   `∑_{k} k³ C(m+1,k)² = (m+1)² · ∑_{j} (j+1) C(m,j)²`.
2. `two_mul_sum_cube_weighted_sq` — the closed form (subtraction-free `m`-form)
   `2 · ∑_{k} k³ C(m+1,k)² = (m+1)² · (m+2) · C(2m, m)`.
3. `two_mul_sum_cube_weighted_sq'` — the classical `n ≥ 1` form
   `2 · ∑_{k} k³ C(n,k)² = n² · (n+1) · C(2n−2, n−1)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ06

open Finset

/-- **Absorption + index-shift reduction.** Squaring the absorption identity
    `k · C(m+1, k) = (m+1) · C(m, k−1)` demotes the cubically-weighted square of
    `C(m+1, ·)` to a *linearly*-weighted square of `C(m, ·)` one order down.  The
    `k = 0` term vanishes, and the shift `k ↦ k+1` turns the residual weight `k`
    into `k + 1`. -/
theorem sum_cube_weighted_sq_reduce (m : ℕ) :
    ∑ k ∈ range (m + 2), k ^ 3 * ((m + 1).choose k) ^ 2
      = (m + 1) ^ 2 * ∑ j ∈ range (m + 1), (j + 1) * (m.choose j) ^ 2 := by
  rw [Finset.sum_range_succ' (fun k => k ^ 3 * ((m + 1).choose k) ^ 2) (m + 1)]
  -- the peeled `k = 0` term is `0 ^ 3 * _ = 0`
  simp only [pow_succ, Nat.mul_zero, Nat.zero_mul, add_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  -- absorption with the index already shifted: (k+1)·C(m+1,k+1) = (m+1)·C(m,k)
  have hab : (k + 1) * ((m + 1).choose (k + 1)) = (m + 1) * (m.choose k) := by
    have h := CombinationsFormulaOQ07OQ01.mul_choose_eq
      (n := m + 1) (k := k + 1) (by omega) (by omega)
    simpa using h
  -- square it to demote the coefficient
  have hsq : (k + 1) ^ 2 * ((m + 1).choose (k + 1)) ^ 2
      = (m + 1) ^ 2 * (m.choose k) ^ 2 := by
    have h2 : ((k + 1) * ((m + 1).choose (k + 1))) ^ 2
        = ((m + 1) * (m.choose k)) ^ 2 := by rw [hab]
    rw [mul_pow, mul_pow] at h2
    exact h2
  calc (k + 1) ^ 3 * ((m + 1).choose (k + 1)) ^ 2
      = (k + 1) * ((k + 1) ^ 2 * ((m + 1).choose (k + 1)) ^ 2) := by ring
    _ = (k + 1) * ((m + 1) ^ 2 * (m.choose k) ^ 2) := by rw [hsq]
    _ = (m + 1) ^ 2 * ((k + 1) * (m.choose k) ^ 2) := by ring

/-- **Cubically weighted central binomial sum of squares** (subtraction-free form).
    `2 · ∑_{k=0}^{m+1} k³ · C(m+1, k)² = (m+1)² · (m+2) · C(2m, m)`.
    The factor of `2` absorbs the first-moment doubling and keeps the statement
    free of natural-number subtraction. -/
theorem two_mul_sum_cube_weighted_sq (m : ℕ) :
    2 * ∑ k ∈ range (m + 2), k ^ 3 * ((m + 1).choose k) ^ 2
      = (m + 1) ^ 2 * (m + 2) * (2 * m).choose m := by
  -- split the linearly-weighted sum into first + zeroth moment at level `m`
  have hsplit : ∑ j ∈ range (m + 1), (j + 1) * (m.choose j) ^ 2
      = (∑ j ∈ range (m + 1), j * (m.choose j) ^ 2)
          + ∑ j ∈ range (m + 1), (m.choose j) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- `2 · S₃` rewritten in terms of the two lower moments
  have hR : 2 * ∑ k ∈ range (m + 2), k ^ 3 * ((m + 1).choose k) ^ 2
      = (m + 1) ^ 2 * (2 * (∑ j ∈ range (m + 1), j * (m.choose j) ^ 2)
          + 2 * ∑ j ∈ range (m + 1), (m.choose j) ^ 2) := by
    rw [sum_cube_weighted_sq_reduce, hsplit]; ring
  -- first moment (OQ-07-OQ-03) and zeroth moment (parent OQ-07) at level `m`
  have hF := CombinationsFormulaOQ07OQ03.two_mul_sum_weighted_sq m
  have hP := (CombinationsFormulaOQ07.central_binom_eq_sum_sq m).symm
  rw [hR, hF, hP]; ring

/-- **Third moment (classical form).** For `n ≥ 1`,
    `2 · ∑_{k=0}^{n} k³ · C(n, k)² = n² · (n + 1) · C(2n − 2, n − 1)`. -/
theorem two_mul_sum_cube_weighted_sq' (n : ℕ) (hn : 1 ≤ n) :
    2 * ∑ k ∈ range (n + 1), k ^ 3 * (n.choose k) ^ 2
      = n ^ 2 * (n + 1) * (2 * n - 2).choose (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (m + 1) - 2 = 2 * m := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1, e2, two_mul_sum_cube_weighted_sq m]

/-- Sanity check: `∑_{k=0}^{3} k³·C(3,k)² = 0 + 9 + 72 + 27 = 108`, and
    `2·108 = 216 = 3²·4·C(4,2) = 9·4·6`. -/
example : ∑ k ∈ range 4, k ^ 3 * ((3 : ℕ).choose k) ^ 2 = 108 := by decide

/-- Sanity check of the closed form at `n = 3`: `2·108 = 3²·4·C(4,2)`. -/
example : 2 * ∑ k ∈ range 4, k ^ 3 * ((3 : ℕ).choose k) ^ 2
    = 3 ^ 2 * (3 + 1) * (2 * 3 - 2).choose (3 - 1) := by decide

end CombinationsFormulaOQ07OQ06
