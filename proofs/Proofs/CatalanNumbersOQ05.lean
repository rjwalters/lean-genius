import Mathlib

/-!
# Catalan numbers as a difference of central binomial coefficients

Mathlib records the Catalan numbers (`catalan`) together with the two
standard *quotient* descriptions of them through the central binomial
coefficient `Nat.centralBinom n = (2n).choose n`:

* `catalan_eq_centralBinom_div` — `catalan n = centralBinom n / (n + 1)`;
* `succ_mul_catalan_eq_centralBinom` — `(n + 1) * catalan n = centralBinom n`.

Both of these involve a division (or the multiplication that clears it). The
classical *subtractive* form of the same fact,

  `catalan n = C(2n, n) − C(2n, n + 1)`,

expresses the Catalan number as the gap between the central binomial coefficient
and its immediate neighbour on the same row of Pascal's triangle. This is the
identity behind André's reflection / ballot-sequence count: the number of
monotone lattice paths staying weakly below the diagonal is the total count of
central paths minus those that cross it. Mathlib does not record it, so this
entry supplies it as a fully machine-checked `ℕ` identity (no division, no
axioms, no `native_decide`).

## Proof outline

Write `a = C(2n, n)`, `b = C(2n, n + 1)`, `c = catalan n`. Two facts pin down
`a` and `b` in terms of `c`:

* `a = (n + 1) · c`               (Mathlib's `succ_mul_catalan_eq_centralBinom`);
* `b · (n + 1) = a · n`           (Mathlib's `choose_succ_right_eq`, since
                                   `2n − n = n`).

Substituting the first into the second and cancelling the positive factor
`n + 1` gives `b = n · c`. Therefore

  `a − b = (n + 1)·c − n·c = c`,

which is the claim. Everything is exact arithmetic in `ℕ`; the only subtraction,
`a − b`, is legitimate because `b ≤ a` (the central coefficient is the row
maximum), and indeed the proof never needs that inequality separately — the
algebra `(n+1)·c − n·c = c` collapses on its own.
-/

namespace CatalanNumbersOQ05

open Nat

/-- The off-diagonal central binomial coefficient `C(2n, n+1)` is exactly
`n · catalan n`. This is the workhorse behind the difference identity. -/
theorem choose_succ_eq_mul_catalan (n : ℕ) :
    (2 * n).choose (n + 1) = n * catalan n := by
  -- `a = (n+1) · catalan n`.
  have ha : (2 * n).choose n = (n + 1) * catalan n := by
    rw [← Nat.centralBinom_eq_two_mul_choose, ← succ_mul_catalan_eq_centralBinom]
  -- `b · (n+1) = a · (2n − n) = a · n`.
  have key : (2 * n).choose (n + 1) * (n + 1) = (2 * n).choose n * n := by
    have h := Nat.choose_succ_right_eq (2 * n) n
    have h2 : 2 * n - n = n := by omega
    rwa [h2] at h
  -- Cancel the positive factor `n + 1`.
  apply Nat.eq_of_mul_eq_mul_right (show 0 < n + 1 by omega)
  rw [key, ha]
  ring

/-- **Catalan numbers as a difference of central binomial coefficients.**
`catalan n = C(2n, n) − C(2n, n + 1)`. -/
theorem catalan_eq_centralBinom_sub (n : ℕ) :
    catalan n = (2 * n).choose n - (2 * n).choose (n + 1) := by
  have ha : (2 * n).choose n = (n + 1) * catalan n := by
    rw [← Nat.centralBinom_eq_two_mul_choose, ← succ_mul_catalan_eq_centralBinom]
  have hb : (2 * n).choose (n + 1) = n * catalan n := choose_succ_eq_mul_catalan n
  rw [ha, hb, Nat.add_one_mul, Nat.add_sub_cancel_left]

/-- The same identity written through `Nat.centralBinom`, matching Mathlib's
preferred spelling of the central coefficient. -/
theorem catalan_eq_centralBinom_sub' (n : ℕ) :
    catalan n = Nat.centralBinom n - (2 * n).choose (n + 1) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  exact catalan_eq_centralBinom_sub n

/-- Sanity checks against the first few Catalan numbers
`1, 1, 2, 5, 14, 42`. -/
example : catalan 0 = (2 * 0).choose 0 - (2 * 0).choose 1 := catalan_eq_centralBinom_sub 0
example : catalan 1 = (2 * 1).choose 1 - (2 * 1).choose 2 := catalan_eq_centralBinom_sub 1
example : catalan 2 = (2 * 2).choose 2 - (2 * 2).choose 3 := catalan_eq_centralBinom_sub 2
example : catalan 3 = (2 * 3).choose 3 - (2 * 3).choose 4 := catalan_eq_centralBinom_sub 3
example : catalan 4 = (2 * 4).choose 4 - (2 * 4).choose 5 := catalan_eq_centralBinom_sub 4

end CatalanNumbersOQ05
