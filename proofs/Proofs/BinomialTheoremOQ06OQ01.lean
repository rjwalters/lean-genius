import Mathlib

/-
# Signed Vandermonde Convolution and the Alternating Squared-Binomial Sum

## Open Question OQ-06-OQ-01 (from `binomial-theorem-oq-06`)

Mathlib records the *unsigned* Vandermonde identity
`∑_{k} C(m,k)·C(n,r-k) = C(m+n,r)` (`Nat.add_choose_eq`) and the plain
alternating row sum `∑_k (-1)^k C(n,k) = [n = 0]`
(`Int.alternating_sum_range_choose`), but not the **signed Vandermonde
convolution** that interpolates between them:

  `∑_{k=0}^{r} (-1)^k C(m,k) C(n,r-k) = [x^r] (1-x)^m (1+x)^n`.

This entry proves that generating-function identity and specialises it to the
classical **alternating sum of squared binomial coefficients**:

  `∑_{k=0}^{n} (-1)^k C(n,k)^2 = 0`  if `n` is odd,
  `∑_{k=0}^{n} (-1)^k C(n,k)^2 = (-1)^{n/2} C(n, n/2)`  if `n` is even,

obtained by setting `m = n` and using `(1-x)(1+x) = 1 - x^2`.

## Results

* `coeff_one_sub_X_pow`      — `[x^k] (1-X)^m = (-1)^k C(m,k)` in `ℤ[X]`;
* `signed_vandermonde`       — the signed convolution equals `[x^r] (1-X)^m (1+X)^n`;
* `signed_vandermonde_diag`  — the `m = n` case equals `[x^r] (1-X^2)^n`;
* `coeff_one_sub_X_sq_pow`   — `[x^r] (1-X^2)^n = [2∣r] (-1)^{r/2} C(n, r/2)`;
* `alternating_choose_sq`    — `∑_k (-1)^k C(n,k)^2 = [x^n] (1-X^2)^n`;
* `alternating_choose_sq_closed` — the closed form
  `∑_k (-1)^k C(n,k)^2 = [2∣n] (-1)^{n/2} C(n, n/2)`;
* `alternating_choose_sq_odd` — the vanishing statement for odd `n`.

## Proof engine

Everything runs through polynomial coefficient extraction over `ℤ[X]`.
The convolution is `Polynomial.coeff_mul` on `(1-X)^m (1+X)^n`, rewritten from
the antidiagonal to `range (r+1)`; the two factor coefficients are
`coeff_one_sub_X_pow` (proved from `coeff_X_add_C_pow` with the sign
identity `(-1)^m (-1)^{m-k} = (-1)^k`) and Mathlib's `coeff_one_add_X_pow`.
The diagonal specialisation collapses the product via `(1-X)(1+X) = 1-X^2`,
whose coefficients come from the binomial expansion
`(1 - X^2)^n = ∑_j (-1)^j C(n,j) X^{2j}`.

## References

- Signed Vandermonde / Vandermonde–Chu convolution (standard generating-function identity).
- Parent `binomial-theorem-oq-06`; sibling `binomial-theorem-oq-06-oq-02` (hockey-stick diagonals).

## Axioms: 0 | Sorries: 0
-/

namespace BinomialTheoremOQ06OQ01

open Polynomial Finset

/-! ## Coefficients of `(1 - X)^m` -/

/-- The sign identity `(-1)^m · (-1)^{m-k} = (-1)^k` for `k ≤ m` (over `ℤ`). -/
theorem neg_one_pow_mul_sub (m k : ℕ) (hk : k ≤ m) :
    (-1 : ℤ) ^ m * (-1) ^ (m - k) = (-1) ^ k := by
  rw [← pow_add, show m + (m - k) = k + 2 * (m - k) from by omega, pow_add, pow_mul]
  simp

/-- `[x^k] (1 - X)^m = (-1)^k · C(m, k)` in `ℤ[X]`. -/
theorem coeff_one_sub_X_pow (m k : ℕ) :
    ((1 - X : ℤ[X]) ^ m).coeff k = (-1) ^ k * (m.choose k : ℤ) := by
  have h : (1 - X : ℤ[X]) = C (-1) * (X + C (-1)) := by
    rw [C_neg, C_1]; ring
  rw [h, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  rcases le_or_gt k m with hkm | hkm
  · rw [← mul_assoc, neg_one_pow_mul_sub m k hkm]
  · rw [Nat.choose_eq_zero_of_lt hkm]; simp

/-! ## The signed Vandermonde convolution -/

/-- **Signed Vandermonde convolution.** For all `m, n, r`,
`∑_{k=0}^{r} (-1)^k C(m,k) C(n,r-k) = [x^r] (1-X)^m (1+X)^n`. -/
theorem signed_vandermonde (m n r : ℕ) :
    ∑ k ∈ range (r + 1), (-1) ^ k * (m.choose k : ℤ) * (n.choose (r - k) : ℤ)
      = ((1 - X : ℤ[X]) ^ m * (1 + X) ^ n).coeff r := by
  rw [coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => ((1 - X : ℤ[X]) ^ m).coeff i * ((1 + X : ℤ[X]) ^ n).coeff j)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [coeff_one_sub_X_pow, coeff_one_add_X_pow]

/-- Diagonal case `m = n`: the convolution equals `[x^r] (1 - X^2)^n`. -/
theorem signed_vandermonde_diag (n r : ℕ) :
    ∑ k ∈ range (r + 1), (-1) ^ k * (n.choose k : ℤ) * (n.choose (r - k) : ℤ)
      = ((1 - X ^ 2 : ℤ[X]) ^ n).coeff r := by
  rw [signed_vandermonde n n r, ← mul_pow]
  congr 2
  ring

/-! ## Coefficients of `(1 - X^2)^n` -/

/-- `(1 - X^2)^n = ∑_{j=0}^{n} (-1)^j C(n,j) X^{2j}` in `ℤ[X]`. -/
theorem one_sub_X_sq_pow_eq (n : ℕ) :
    (1 - X ^ 2 : ℤ[X]) ^ n
      = ∑ j ∈ range (n + 1), C ((-1) ^ j * (n.choose j : ℤ)) * X ^ (2 * j) := by
  have h : (1 - X ^ 2 : ℤ[X]) = -X ^ 2 + 1 := by ring
  rw [h, add_pow]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [one_pow, mul_one, neg_pow, ← pow_mul, C_mul, C_pow, C_neg, C_1, C_eq_natCast]
  ring

/-- **Closed form for `(1 - X^2)^n` coefficients.**
`[x^r] (1 - X^2)^n = (-1)^{r/2} C(n, r/2)` when `2 ∣ r`, and `0` otherwise. -/
theorem coeff_one_sub_X_sq_pow (n r : ℕ) :
    ((1 - X ^ 2 : ℤ[X]) ^ n).coeff r
      = if 2 ∣ r then (-1) ^ (r / 2) * (n.choose (r / 2) : ℤ) else 0 := by
  rw [one_sub_X_sq_pow_eq, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hr : 2 ∣ r
  · rw [if_pos hr]
    obtain ⟨t, rfl⟩ := hr
    rw [Nat.mul_div_cancel_left t (by norm_num)]
    rw [Finset.sum_eq_single t]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg]; omega
    · intro ht
      rw [Finset.mem_range, not_lt] at ht
      rw [if_pos rfl, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · rw [if_neg hr]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg]
    intro h; exact hr ⟨j, h⟩

/-! ## The alternating sum of squared binomial coefficients -/

/-- The convolution at `r = n` is the alternating sum of squared binomials. -/
theorem alternating_choose_sq (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℤ) ^ 2
      = ((1 - X ^ 2 : ℤ[X]) ^ n).coeff n := by
  rw [← signed_vandermonde_diag n n]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [Nat.choose_symm hk]
  ring

/-- **Closed form.** `∑_{k=0}^{n} (-1)^k C(n,k)^2 = (-1)^{n/2} C(n, n/2)` for even
`n`, and `0` for odd `n`. -/
theorem alternating_choose_sq_closed (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℤ) ^ 2
      = if 2 ∣ n then (-1) ^ (n / 2) * (n.choose (n / 2) : ℤ) else 0 := by
  rw [alternating_choose_sq, coeff_one_sub_X_sq_pow]

/-- **Vanishing for odd `n`.** `∑_{k=0}^{n} (-1)^k C(n,k)^2 = 0` when `n` is odd. -/
theorem alternating_choose_sq_odd (n : ℕ) (hn : Odd n) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℤ) ^ 2 = 0 := by
  rw [alternating_choose_sq_closed, if_neg]
  simpa [Nat.two_dvd_ne_zero, Nat.odd_iff] using hn

/-! ## Numerical sanity checks -/

/-- `∑_{k=0}^{4} (-1)^k C(4,k)^2 = 1 - 16 + 36 - 16 + 1 = 6 = (-1)^2 C(4,2)`. -/
theorem check_four :
    ∑ k ∈ range 5, (-1) ^ k * ((4).choose k : ℤ) ^ 2 = 6 := by decide

/-- `∑_{k=0}^{3} (-1)^k C(3,k)^2 = 1 - 9 + 9 - 1 = 0` (odd case). -/
theorem check_three :
    ∑ k ∈ range 4, (-1) ^ k * ((3).choose k : ℤ) ^ 2 = 0 := by decide

#print axioms signed_vandermonde
#print axioms coeff_one_sub_X_sq_pow
#print axioms alternating_choose_sq_closed
#print axioms alternating_choose_sq_odd

end BinomialTheoremOQ06OQ01
