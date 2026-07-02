/-
# Vandermonde's convolution identity and its diagonal corollaries

Parent: `binomial-theorem` (open question — Vandermonde's identity).

Mathlib proves Vandermonde's identity in *antidiagonal* form,
`Nat.add_choose_eq`:

  (m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2,

obtained by comparing the `X^k` coefficient in (X+1)^m·(X+1)^n = (X+1)^(m+n)
(the generating-function / algebraic proof).

This entry does two things Mathlib does not.

1. It repackages the identity in the *classical textbook range form*

     C(m+n, r) = ∑_{k=0}^{r} C(m, k)·C(n, r−k),                (`vandermonde_range`)

   a single-index convolution over `Finset.range (r+1)`, which is the shape in
   which the identity is normally stated and used.

2. It derives the two famous *diagonal* corollaries that are **absent from
   Mathlib**:

     ∑_{k=0}^{n} C(m, k)·C(n, k) = C(m+n, n),                  (`sum_choose_mul_choose`)
     ∑_{k=0}^{n} C(n, k)²       = C(2n, n) = centralBinom n.   (`sum_sq_choose`)

   The second says: summing the squares of a row of Pascal's triangle gives the
   central binomial coefficient. It is the `m = n` case of the first, which is
   itself Vandermonde after flipping one factor with the symmetry C(n,k)=C(n,n−k).

Verified: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
import Mathlib

open Finset BigOperators

namespace VandermondeConvolutionOQ06

/-! ## Vandermonde's identity: antidiagonal and range forms -/

/-- Vandermonde's identity in antidiagonal form, restating Mathlib's
`Nat.add_choose_eq` (proved by coefficient comparison in (X+1)^m·(X+1)^n) for
reference and as the bridge to the range form below. -/
theorem vandermonde_antidiagonal (m n r : ℕ) :
    (m + n).choose r
      = ∑ ij ∈ Finset.antidiagonal r, m.choose ij.1 * n.choose ij.2 :=
  Nat.add_choose_eq m n r

/-- **Vandermonde's identity, classical range form.**
`C(m+n, r) = ∑_{k=0}^{r} C(m,k)·C(n, r−k)`. This is the single-index convolution
statement; we obtain it from the antidiagonal form by reindexing the
antidiagonal of `r` as `k ↦ (k, r−k)` over `range (r+1)`. -/
theorem vandermonde_range (m n r : ℕ) :
    (m + n).choose r
      = ∑ k ∈ range (r + 1), m.choose k * n.choose (r - k) := by
  rw [vandermonde_antidiagonal,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun ij => m.choose ij.1 * n.choose ij.2) r]

/-! ## Diagonal corollaries (not in Mathlib) -/

/-- **Symmetric product form.** `∑_{k=0}^{n} C(m,k)·C(n,k) = C(m+n, n)`.
Apply Vandermonde with `r = n` and flip the second factor with the symmetry
`C(n, n−k) = C(n, k)` (valid since `k ≤ n` on the summation range). -/
theorem sum_choose_mul_choose (m n : ℕ) :
    ∑ k ∈ range (n + 1), m.choose k * n.choose k = (m + n).choose n := by
  rw [vandermonde_range m n n]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [mem_range, Nat.lt_succ_iff] at hk
  rw [Nat.choose_symm hk]

/-- The symmetric product form with the split written as `C(m+n, m)`, using
`C(m+n, m) = C(m+n, n)`. -/
theorem sum_choose_mul_choose' (m n : ℕ) :
    ∑ k ∈ range (n + 1), m.choose k * n.choose k = (m + n).choose m := by
  rw [sum_choose_mul_choose, Nat.choose_symm_add]

/-- **Sum of squares of a Pascal row is the central binomial coefficient:**
`∑_{k=0}^{n} C(n,k)² = C(2n, n)`. The `m = n` diagonal case of
`sum_choose_mul_choose`. -/
theorem sum_sq_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = (2 * n).choose n := by
  rw [two_mul, ← sum_choose_mul_choose n n]
  exact Finset.sum_congr rfl (fun k _ => pow_two (n.choose k))

/-- The sum-of-squares identity phrased through Mathlib's `Nat.centralBinom`:
`∑_{k=0}^{n} C(n,k)² = centralBinom n`. -/
theorem sum_sq_choose_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = n.centralBinom := by
  rw [sum_sq_choose]
  rfl

/-! ## Worked examples -/

/-- `C(5,2) = C(2,0)C(3,2) + C(2,1)C(3,1) + C(2,2)C(3,0) = 0 + 6 + 1 = ...`,
the range form for `m=2, n=3, r=2`. -/
example : (2 + 3).choose 2 = ∑ k ∈ range 3, (2 : ℕ).choose k * (3 : ℕ).choose (2 - k) :=
  vandermonde_range 2 3 2

/-- `∑_{k=0}^{3} C(3,k)² = C(6,3)` (equals 20): the sum-of-squares corollary. -/
example : ∑ k ∈ range 4, ((3 : ℕ).choose k) ^ 2 = (2 * 3).choose 3 :=
  sum_sq_choose 3

/-- Numeric check of the sum-of-squares value: `1² + 3² + 3² + 1² = 20`. -/
example : ∑ k ∈ range 4, ((3 : ℕ).choose k) ^ 2 = 20 := by
  rw [sum_sq_choose 3]; rfl

end VandermondeConvolutionOQ06
