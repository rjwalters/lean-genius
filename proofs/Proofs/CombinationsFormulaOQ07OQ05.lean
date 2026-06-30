import Mathlib
import Proofs.CombinationsFormulaOQ07

/-
# The Alternating Sum of Squares of Binomial Coefficients

## Open Question OQ-07 → OQ-05

The parent problem `combinations-formula-oq-07` proves the **central binomial
sum-of-squares**, the diagonal of Vandermonde's convolution:

  ∑_{k=0}^{n} C(n, k)² = C(2n, n).

This file treats its **signed companion**, the alternating sum of squares

  S(n) := ∑_{k=0}^{n} (-1)^k · C(n, k)²,

which is *not* available in Mathlib (Mathlib has only the linear alternating sum
`Int.alternating_sum_range_choose`, i.e. ∑ (-1)^k C(n,k) = [n = 0]).

The signed sum exhibits a sharp **even/odd dichotomy**:

  S(n) = 0                       if n is odd,
  S(2m) = (-1)^m · C(2m, m)      if n = 2m is even.

Equivalently, in one closed form,

  S(n) = if 2 ∣ n then (-1)^{n/2} · C(n, n/2) else 0.

## Two independent proofs

* **Generating function (`alt_sum_sq`).**  The whole dichotomy falls out of one
  coefficient comparison.  Over ℤ[X],
        (1 - X)^n · (1 + X)^n = (1 - X²)^n.
  Reading off the coefficient of `X^n`:
    - the left side, expanded by `coeff_mul` and the binomial coefficients of
      `(1 ± X)^n`, collapses (via `C(n, n-k) = C(n, k)`) to exactly `S(n)`;
    - the right side is a polynomial in `X²`, so its `X^n` coefficient is
      detected by `Polynomial.coeff_expand`: it vanishes unless `2 ∣ n`, in
      which case it equals `(-1)^{n/2} C(n, n/2)`.

* **Reflection / antisymmetry (`alt_sum_sq_odd_reflect`).**  For the odd case
  there is a one-line conceptual reason: substituting `k ↦ n - k` and using
  `C(n, n-k) = C(n, k)` together with `(-1)^{n-k} = -(-1)^k` (valid because `n`
  is odd) shows `S(n) = -S(n)`, hence `S(n) = 0`.  This is the signed analogue
  of the fact that the rows of Pascal's triangle are symmetric.

## Mathematical context

`S(n)` is the coefficient of `X^n` in `(1 - X²)^n`; the dichotomy is the
statement that the "central" coefficient of a polynomial in `X²` only survives
in even degree.  The even value `(-1)^m C(2m, m)` is, up to sign, the central
binomial coefficient — the same quantity the *unsigned* sum produces — so the
alternation precisely sieves out a single signed central term.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ05

open Finset Polynomial

/-- **Coefficients of `(1 - X)^n`.**  `((1 - X)^n).coeff k = (-1)^k · C(n, k)`.
    Derived from `coeff_X_add_C_pow` after writing `1 - X = -(X + C (-1))`. -/
theorem coeff_one_sub_X_pow (n k : ℕ) :
    ((1 - X : ℤ[X]) ^ n).coeff k = (-1) ^ k * (n.choose k : ℤ) := by
  have h1 : (1 - X : ℤ[X]) = -(X + C (-1 : ℤ)) := by
    rw [map_neg, map_one]; ring
  rw [h1, neg_pow,
      show (-1 : ℤ[X]) ^ n = C ((-1 : ℤ) ^ n) by rw [map_pow, map_neg, map_one],
      coeff_C_mul, coeff_X_add_C_pow]
  rcases le_or_gt k n with hkn | hkn
  · rw [← mul_assoc, ← pow_add, show n + (n - k) = 2 * (n - k) + k from by omega,
        pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
  · rw [Nat.choose_eq_zero_of_lt hkn]; simp

/-- **The alternating sum of squares is the `X^n`-coefficient of `(1 - X²)^n`.**
    Uses the factorization `(1 - X²)^n = (1 - X)^n · (1 + X)^n`, `coeff_mul`,
    and the symmetry `C(n, n-k) = C(n, k)`. -/
theorem alt_sum_sq_eq_coeff (n : ℕ) :
    (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2)
      = ((1 - X ^ 2 : ℤ[X]) ^ n).coeff n := by
  have hfac : (1 - X ^ 2 : ℤ[X]) ^ n = (1 - X) ^ n * (1 + X) ^ n := by
    rw [← mul_pow]; congr 1; ring
  rw [hfac, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => ((1 - X : ℤ[X]) ^ n).coeff i * ((1 + X : ℤ[X]) ^ n).coeff j) n]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [coeff_one_sub_X_pow, coeff_one_add_X_pow ℤ, Nat.choose_symm hk]
  ring

/-- **The diagonal coefficient of `(1 - X²)^n`.**  Since `(1 - X²)^n` is a
    polynomial in `X²`, namely `expand ℤ 2 ((1 - X)^n)`, its `X^n` coefficient is
    nonzero only in even degree, where `coeff_expand` reads it off. -/
theorem coeff_one_sub_X_sq_pow_diag (n : ℕ) :
    ((1 - X ^ 2 : ℤ[X]) ^ n).coeff n
      = if 2 ∣ n then (-1) ^ (n / 2) * (n.choose (n / 2) : ℤ) else 0 := by
  have hbase : (1 - X ^ 2 : ℤ[X]) = expand ℤ 2 (1 - X) := by
    rw [map_sub, map_one, expand_X]
  have hexp : (1 - X ^ 2 : ℤ[X]) ^ n = expand ℤ 2 ((1 - X) ^ n) := by
    rw [map_pow, ← hbase]
  rw [hexp, coeff_expand (by norm_num : (0 : ℕ) < 2)]
  split_ifs with h
  · rw [coeff_one_sub_X_pow]
  · rfl

/-- **Main theorem (generating-function proof).**  The closed form for the
    alternating sum of squares of binomial coefficients:
        ∑_{k=0}^{n} (-1)^k C(n,k)² = if 2 ∣ n then (-1)^{n/2} C(n, n/2) else 0. -/
theorem alt_sum_sq (n : ℕ) :
    (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2)
      = if 2 ∣ n then (-1) ^ (n / 2) * (n.choose (n / 2) : ℤ) else 0 := by
  rw [alt_sum_sq_eq_coeff, coeff_one_sub_X_sq_pow_diag]

/-- **Odd case (corollary).**  For odd `n`, the alternating sum of squares
    vanishes. -/
theorem alt_sum_sq_odd {n : ℕ} (hn : Odd n) :
    (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) = 0 := by
  have h2 : ¬ (2 ∣ n) := by
    obtain ⟨j, hj⟩ := hn; rw [hj]; omega
  rw [alt_sum_sq, if_neg h2]

/-- **Even case (corollary).**  For `n = 2m`, the alternating sum of squares
    equals the signed central binomial coefficient `(-1)^m C(2m, m)`. -/
theorem alt_sum_sq_even (m : ℕ) :
    (∑ k ∈ range (2 * m + 1), (-1 : ℤ) ^ k * ((2 * m).choose k : ℤ) ^ 2)
      = (-1) ^ m * ((2 * m).choose m : ℤ) := by
  rw [alt_sum_sq (2 * m), if_pos (dvd_mul_right 2 m),
      Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]

/-- **Odd case, second proof (reflection / antisymmetry).**  Independent of the
    polynomial machinery: substituting `k ↦ n - k` (`Finset.sum_range_reflect`)
    together with `C(n, n-k) = C(n, k)` and `(-1)^{n-k} = -(-1)^k` for odd `n`
    shows the sum equals its own negation. -/
theorem alt_sum_sq_odd_reflect {n : ℕ} (hn : Odd n) :
    (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) = 0 := by
  have hsum : (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2)
      = ∑ k ∈ range (n + 1), -((-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) := by
    rw [← Finset.sum_range_reflect
          (fun k => (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) (n + 1)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hidx : n + 1 - 1 - k = n - k := by omega
    have hsign : (-1 : ℤ) ^ (n - k) = -((-1) ^ k) := by
      have ha : (-1 : ℤ) ^ (n - k) * (-1) ^ k = -1 := by
        rw [← pow_add, Nat.sub_add_cancel hk, hn.neg_one_pow]
      have hb : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by
        rw [← pow_add, ← two_mul]; exact Even.neg_one_pow ⟨k, two_mul k⟩
      calc (-1 : ℤ) ^ (n - k)
            = (-1) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by rw [hb, mul_one]
        _ = ((-1) ^ (n - k) * (-1) ^ k) * (-1) ^ k := by ring
        _ = (-1) * (-1) ^ k := by rw [ha]
        _ = -((-1) ^ k) := by ring
    show (-1 : ℤ) ^ (n + 1 - 1 - k) * (n.choose (n + 1 - 1 - k) : ℤ) ^ 2
        = -((-1) ^ k * (n.choose k : ℤ) ^ 2)
    rw [hidx, Nat.choose_symm hk, hsign]; ring
  rw [Finset.sum_neg_distrib] at hsum
  linarith

/-- Sanity check: `n = 2` gives `1 - 4 + 1 = -2 = (-1)^1 · C(2, 1)`. -/
example : (∑ k ∈ Finset.range (2 * 1 + 1), (-1 : ℤ) ^ k * ((2 * 1).choose k : ℤ) ^ 2) = -2 := by
  rw [alt_sum_sq_even 1]; decide

/-- Sanity check: `n = 4` gives `1 - 16 + 36 - 16 + 1 = 6 = (-1)^2 · C(4, 2)`. -/
example : (∑ k ∈ Finset.range (2 * 2 + 1), (-1 : ℤ) ^ k * ((2 * 2).choose k : ℤ) ^ 2) = 6 := by
  rw [alt_sum_sq_even 2]; decide

/-- Sanity check: `n = 3` (odd) gives `1 - 9 + 9 - 1 = 0`. -/
example : (∑ k ∈ Finset.range (3 + 1), (-1 : ℤ) ^ k * ((3).choose k : ℤ) ^ 2) = 0 :=
  alt_sum_sq_odd (by decide)

end CombinationsFormulaOQ07OQ05
