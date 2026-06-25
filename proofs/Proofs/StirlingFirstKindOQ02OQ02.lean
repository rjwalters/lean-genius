/-
Stirling Numbers of the First Kind, III: the ALTERNATING row sum
  ∑ₖ (−1)ᵏ c(n,k) = (ascPochhammer ℤ n).eval (−1),
which vanishes for every n ≥ 2.

Source: Follow-up open question to stirling-first-kind-oq-02 (the rising-factorial
generating identity c(n,k) = [Xᵏ] ascPochhammer ℤ n).
Status: VERIFIED (0 axioms, 0 sorries)

`Nat.stirlingFirst n k` is the unsigned Stirling number of the first kind: the
number of permutations of an n-element set with exactly k disjoint cycles. The
parent gallery entry `stirling-first-kind-oq-02` proved the generating identity

      X(X+1)(X+2)⋯(X+n−1)  =  ∑ₖ c(n,k)·Xᵏ,        i.e.
      (ascPochhammer ℤ n).coeff k  =  c(n,k),

and recovered the ORDINARY row sum ∑ₖ c(n,k) = n! by evaluating the polynomial at
X = 1 (every Xᵏ ↦ 1, collapsing the coefficient list to its sum).

This entry asks the complementary question: what happens at the OTHER unit, X = −1?
Now Xᵏ ↦ (−1)ᵏ, so the same collapse turns the polynomial value into the
*alternating* row sum:

      ∑ₖ (−1)ᵏ c(n,k)  =  (ascPochhammer ℤ n).eval (−1).

The rising factorial `ascPochhammer ℤ n = X(X+1)⋯(X+n−1)` contains the factor
`(X + 1)` as soon as n ≥ 2, and that factor vanishes at X = −1. Hence the product
is zero for every n ≥ 2:

      ∑ₖ (−1)ᵏ c(n,k)  =  0      (n ≥ 2),

while the two small rows are exceptional: n = 0 gives 1 (empty product), n = 1 gives
−1 (the single factor X at −1). Equivalently, since the SIGNED Stirling number is
s(n,k) = (−1)^{n−k} c(n,k), the identity says the signed row sum ∑ₖ s(n,k) is 0 for
n ≥ 2 — the well-known statement that the falling factorial x(x−1)⋯(x−n+1) vanishes
at x = 1 for n ≥ 2.

We prove:
1. `stirlingFirst_eq_ascPochhammer_coeff` — c(n,k) = [Xᵏ] ascPochhammer ℤ n
                                            (the parent's generating identity).
2. `alternating_row_sum_eq_eval`   — ∑ₖ (−1)ᵏ c(n,k) = (ascPochhammer ℤ n).eval (−1)
                                     for all n (the generating-function reduction).
3. `ascPochhammer_eval_neg_one`    — (ascPochhammer ℤ (m+2)).eval (−1) = 0.
4. `alternating_row_sum_eq_zero`   — ∑ₖ (−1)ᵏ c(n,k) = 0 for n ≥ 2 (the headline).
5. `alternating_row_sum_zero`,
   `alternating_row_sum_one`       — the two exceptional small rows: 1 and −1.
6. `alternating_row_four`          — numeric sanity check: 0 − 6 + 11 − 6 + 1 = 0.
-/

import Mathlib

open Nat Polynomial

namespace StirlingFirstKindOQ02OQ02

/-- The unsigned Stirling number `c(n,k)` is the `Xᵏ`-coefficient of the rising
factorial `ascPochhammer ℤ n` (the generating identity of `stirling-first-kind-oq-02`).
Reproved here so this file is self-contained.

Proof by induction on `n`, using `ascPochhammer ℤ (n+1) = ascPochhammer ℤ n · (X + n)`
(`ascPochhammer_succ_right`): `coeff_mul_X` (index shift) and `coeff_mul_C` reproduce
the Pascal recurrence `c(n+1,k+1) = n·c(n,k+1) + c(n,k)`. -/
theorem stirlingFirst_eq_ascPochhammer_coeff (n k : ℕ) :
    (ascPochhammer ℤ n).coeff k = (Nat.stirlingFirst n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    rw [ascPochhammer_zero, Polynomial.coeff_one]
    cases k with
    | zero => simp
    | succ k => simp [Nat.stirlingFirst_zero_succ]
  | succ n ih =>
    rw [ascPochhammer_succ_right, ← Polynomial.C_eq_natCast, mul_add,
      Polynomial.coeff_add, Polynomial.coeff_mul_C]
    cases k with
    | zero =>
      rw [Polynomial.coeff_mul_X_zero, zero_add, ih, Nat.stirlingFirst_succ_zero]
      have hz : Nat.stirlingFirst n 0 * n = 0 := by
        cases n with
        | zero => simp
        | succ m => simp [Nat.stirlingFirst_succ_zero]
      push_cast
      exact_mod_cast hz
    | succ j =>
      rw [Polynomial.coeff_mul_X, ih, ih, Nat.stirlingFirst_succ_succ]
      push_cast
      ring

/-- **Alternating row sum as a polynomial value.** `∑_{k=0}^{n} (−1)ᵏ c(n,k)` equals
the rising factorial evaluated at `X = −1`.

`(ascPochhammer ℤ n).eval (−1)` expands (`eval_eq_sum_range`,
`ascPochhammer_natDegree`) as `∑_{k<n+1} coeff k · (−1)ᵏ`; replacing each coefficient
by `c(n,k)` via the generating identity gives the alternating sum. This is the exact
analogue of the parent's `X = 1` route for the ordinary row sum. -/
theorem alternating_row_sum_eq_eval (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (Nat.stirlingFirst n k : ℤ)
      = (ascPochhammer ℤ n).eval (-1) := by
  rw [Polynomial.eval_eq_sum_range, ascPochhammer_natDegree ℤ n]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [stirlingFirst_eq_ascPochhammer_coeff n k]
  ring

/-- **The rising factorial vanishes at `−1` from `n = 2` on.** Induction on `m`.

Base `m = 0`: `ascPochhammer ℤ 2 = X·(X+1)` (two applications of `ascPochhammer_succ_right`
off `ascPochhammer ℤ 0 = 1`), whose value at `−1` is `(−1)·0 = 0`.

Step: `ascPochhammer ℤ (m+3) = ascPochhammer ℤ (m+2) · (X + (m+2))`
(`ascPochhammer_succ_right`), so its value at `−1` is `0 · (…) = 0` by the induction
hypothesis — the already-present `(X+1)` factor keeps the product zero. -/
theorem ascPochhammer_eval_neg_one (m : ℕ) :
    (ascPochhammer ℤ (m + 2)).eval (-1 : ℤ) = 0 := by
  induction m with
  | zero =>
    rw [ascPochhammer_succ_right, ascPochhammer_succ_right, ascPochhammer_zero]
    simp [Polynomial.eval_mul]
  | succ k ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, ih, zero_mul]

/-- **Headline: the alternating row sum vanishes for `n ≥ 2`.**
`∑_{k=0}^{n} (−1)ᵏ c(n,k) = 0`. Combine the generating-function reduction (theorem 2)
with the vanishing of `ascPochhammer ℤ n` at `−1` (theorem 3). -/
theorem alternating_row_sum_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (Nat.stirlingFirst n k : ℤ) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [alternating_row_sum_eq_eval, Nat.add_comm 2 m]
  exact ascPochhammer_eval_neg_one m

/-- **Exceptional small row `n = 0`.** The empty product gives alternating sum `1`. -/
theorem alternating_row_sum_zero :
    ∑ k ∈ Finset.range 1, (-1 : ℤ) ^ k * (Nat.stirlingFirst 0 k : ℤ) = 1 := by
  simp [Nat.stirlingFirst]

/-- **Exceptional small row `n = 1`.** The single factor `X` at `−1` gives `−1`. -/
theorem alternating_row_sum_one :
    ∑ k ∈ Finset.range 2, (-1 : ℤ) ^ k * (Nat.stirlingFirst 1 k : ℤ) = -1 := by
  simp [Finset.sum_range_succ, Nat.stirlingFirst]

/-- **Numeric sanity check.** Row 4 is `c(4,0..4) = 0, 6, 11, 6, 1`; the alternating
sum is `0 − 6 + 11 − 6 + 1 = 0`, matching `alternating_row_sum_eq_zero`. -/
theorem alternating_row_four :
    ∑ k ∈ Finset.range 5, (-1 : ℤ) ^ k * (Nat.stirlingFirst 4 k : ℤ) = 0 := by
  simp [Finset.sum_range_succ, Nat.stirlingFirst]

end StirlingFirstKindOQ02OQ02
