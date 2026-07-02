/-
# Hockey-stick (Zhu Shijie) diagonal sums and the Catalan / lattice-path bridge

Parent: `binomial-theorem-oq-06` — *Vandermonde's convolution identity and its
diagonal corollaries* (`∑ C(n,k)² = C(2n,n)`).

This entry answers that parent's second open question:

> Formalize the hockey-stick and Li Jen-Shu identities as further diagonal sums,
> and connect `∑ C(n,k)² = C(2n,n)` to the lattice-path / Catalan-number
> interpretation.

## What Mathlib already provides

Mathlib proves the **hockey-stick identity** (Zhu Shijie / 朱世傑) in two forms,
each fixing the *lower* index `k` and summing a **vertical** slice of Pascal's
triangle:

* `Nat.sum_Icc_choose       : ∑_{m ∈ [k,n]} C(m,k) = C(n+1, k+1)`
* `Nat.sum_range_add_choose : ∑_{i ≤ n}     C(i+k,k) = C(n+k+1, k+1)`

## What this entry adds (absent from Mathlib)

1. **Parallel-summation / diagonal hockey-stick** (`parallel_summation`,
   `parallel_summation'`):

     `∑_{k=0}^{n} C(r+k, k) = C(r+n+1, r+1) = C(r+n+1, n)`.

   Here the *difference* `(r+k) − k = r` is constant, so the summands run down a
   **diagonal** of Pascal's triangle; the value is the lattice-path count
   `C(r+n+1, n)`. This is the "Li Jen-Shu" companion of the vertical
   hockey-stick, obtained by flipping each summand with `C(r+k,k) = C(r+k,r)`.

2. **Central diagonal** (`central_diagonal`):

     `∑_{k=0}^{n} C(n+k, k) = C(2n+1, n)`,

   the `r = n` case — a partial diagonal sum landing on the central column.

3. **Catalan / lattice-path bridge**. Re-deriving the Vandermonde diagonal
   `∑ C(n,k)² = C(2n,n) = centralBinom n` and combining it with Mathlib's
   `succ_mul_catalan_eq_centralBinom` yields the identities **not in Mathlib**:

     `∑_{k=0}^{n} C(n,k)² = (n+1) · catalan n`   (`sum_sq_choose_eq_succ_mul_catalan`)
     `catalan n = (∑_{k=0}^{n} C(n,k)²) / (n+1)` (`catalan_eq_sum_sq_choose_div`).

   Interpretation: `C(2n,n)` counts monotone NE lattice paths `(0,0) → (n,n)`;
   the Catalan number `catalan n` counts those staying weakly below the diagonal,
   and each such path is shared `n+1` times under cyclic rotation (the cycle
   lemma), which is exactly the factor `n+1`.

Verified: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
import Mathlib

open Finset BigOperators

namespace HockeyStickCatalanOQ0602

/-! ## 1. Hockey-stick identity (restating Mathlib as the bridge) -/

/-- **Hockey-stick / Zhu Shijie, `Icc` form** (Mathlib's `Nat.sum_Icc_choose`):
`∑_{m ∈ [k,n]} C(m,k) = C(n+1, k+1)`. A vertical slice of Pascal's triangle. -/
theorem hockey_stick_Icc (n k : ℕ) :
    ∑ m ∈ Icc k n, m.choose k = (n + 1).choose (k + 1) :=
  Nat.sum_Icc_choose n k

/-- **Hockey-stick / Zhu Shijie, `range` form** (Mathlib's `Nat.sum_range_add_choose`):
`∑_{i=0}^{n} C(i+k, k) = C(n+k+1, k+1)`. -/
theorem hockey_stick_range (n k : ℕ) :
    ∑ i ∈ range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1) :=
  Nat.sum_range_add_choose n k

/-! ## 2. Diagonal corollaries (absent from Mathlib) -/

/-- **Parallel-summation / diagonal hockey-stick.**
`∑_{k=0}^{n} C(r+k, k) = C(r+n+1, r+1)`. The summands `C(r+k,k)` lie on the
diagonal of Pascal's triangle with constant difference `r`. We flip each
summand via `C(r+k,k) = C(k+r,r)` (`Nat.choose_symm_add`) to land on the
vertical hockey-stick. -/
theorem parallel_summation (r n : ℕ) :
    ∑ k ∈ range (n + 1), (r + k).choose k = (r + n + 1).choose (r + 1) := by
  have h : (∑ k ∈ range (n + 1), (r + k).choose k)
      = ∑ k ∈ range (n + 1), (k + r).choose r :=
    Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm r k, Nat.choose_symm_add])
  rw [h, Nat.sum_range_add_choose n r, Nat.add_comm n r]

/-- The same diagonal sum written with the lattice-path count `C(r+n+1, n)`,
using `C(r+n+1, r+1) = C(r+n+1, n)`. -/
theorem parallel_summation' (r n : ℕ) :
    ∑ k ∈ range (n + 1), (r + k).choose k = (r + n + 1).choose n := by
  have e : r + n + 1 = (r + 1) + n := by ring
  rw [parallel_summation, e]
  exact Nat.choose_symm_add

/-- **Central diagonal.** `∑_{k=0}^{n} C(n+k, k) = C(2n+1, n)`: the `r = n` case
of `parallel_summation'`, a partial diagonal sum landing on the central column. -/
theorem central_diagonal (n : ℕ) :
    ∑ k ∈ range (n + 1), (n + k).choose k = (2 * n + 1).choose n := by
  rw [parallel_summation' n n, two_mul]

/-! ## 3. Vandermonde diagonal `∑ C(n,k)² = C(2n,n)` (self-contained) -/

/-- **Sum of squares of a Pascal row is the central binomial coefficient:**
`∑_{k=0}^{n} C(n,k)² = C(2n, n)`. Proved directly from Vandermonde
(`Nat.add_choose_eq`) by flipping one factor with `C(n,n−k) = C(n,k)`. -/
theorem sum_sq_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = (2 * n).choose n := by
  have key : (n + n).choose n
      = ∑ k ∈ range (n + 1), n.choose k * n.choose (n - k) := by
    rw [Nat.add_choose_eq n n n,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij => n.choose ij.1 * n.choose ij.2) n]
  rw [two_mul, key]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [mem_range, Nat.lt_succ_iff] at hk
  rw [pow_two, Nat.choose_symm hk]

/-- `∑_{k=0}^{n} C(n,k)² = centralBinom n`, phrased through `Nat.centralBinom`. -/
theorem sum_sq_choose_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = n.centralBinom := by
  rw [sum_sq_choose]; rfl

/-! ## 4. Catalan / lattice-path bridge (absent from Mathlib) -/

/-- **Catalan bridge.** `∑_{k=0}^{n} C(n,k)² = (n+1) · catalan n`.
Combines `sum_sq_choose_centralBinom` with Mathlib's
`succ_mul_catalan_eq_centralBinom`. The factor `n+1` is the cycle-lemma
multiplicity: each Dyck path (below-diagonal lattice path) is shared `n+1`
times among all `C(2n,n)` monotone paths from `(0,0)` to `(n,n)`. -/
theorem sum_sq_choose_eq_succ_mul_catalan (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = (n + 1) * catalan n := by
  rw [sum_sq_choose_centralBinom, succ_mul_catalan_eq_centralBinom]

/-- The Catalan number as the sum-of-squares divided by `n+1`:
`catalan n = (∑_{k=0}^{n} C(n,k)²) / (n+1)`. -/
theorem catalan_eq_sum_sq_choose_div (n : ℕ) :
    catalan n = (∑ k ∈ range (n + 1), (n.choose k) ^ 2) / (n + 1) := by
  rw [sum_sq_choose_centralBinom, catalan_eq_centralBinom_div]

/-! ## Worked examples -/

/-- Vertical hockey-stick: `C(2,2)+C(3,2)+C(4,2)+C(5,2) = 1+3+6+10 = 20 = C(6,3)`. -/
example : ∑ m ∈ Icc 2 5, m.choose 2 = (5 + 1).choose 3 := hockey_stick_Icc 5 2

/-- Diagonal hockey-stick: `C(2,0)+C(3,1)+C(4,2) = 1+3+6 = 10 = C(5,2)`. -/
example : ∑ k ∈ range 3, (2 + k).choose k = (2 + 2 + 1).choose 2 := parallel_summation' 2 2

/-- Central diagonal: `C(3,0)+C(4,1)+C(5,2)+C(6,3) = 1+4+10+20 = 35 = C(7,3)`. -/
example : ∑ k ∈ range 4, (3 + k).choose k = (2 * 3 + 1).choose 3 := central_diagonal 3

/-- Numeric check of the central-diagonal value. -/
example : ∑ k ∈ range 4, (3 + k).choose k = 35 := by decide

/-- Catalan bridge at `n = 4`: `∑ C(4,k)² = 1+16+36+16+1 = 70 = 5 · catalan 4 = 5·14`. -/
example : ∑ k ∈ range 5, ((4 : ℕ).choose k) ^ 2 = 5 * catalan 4 :=
  sum_sq_choose_eq_succ_mul_catalan 4

/-- Numeric check: `∑ C(4,k)² = 70`. -/
example : ∑ k ∈ range 5, ((4 : ℕ).choose k) ^ 2 = 70 := by decide

end HockeyStickCatalanOQ0602
