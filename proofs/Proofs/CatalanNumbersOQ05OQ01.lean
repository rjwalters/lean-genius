/-
# The Catalan Number as a Difference of Central Binomial Coefficients (Ballot Number)

## Open question (`catalan-numbers-oq-05-oq-01`)

The parent entry `catalan-numbers-oq-05` works with the Catalan numbers via Mathlib's
explicit formula `catalan n = C(2n,n)/(n+1)`. Its open question asks for the
*row-difference* form: `catalan n` as a reflected difference of binomial coefficients —
the **ballot numbers** `C(2n,n−k) − C(2n,n−k−1)` — exhibiting the Catalan triangle as
successive differences.

## Result

The base ballot number (`k = 0`) is the clean closed identity

    catalan n = C(2n, n) − C(2n, n+1),

i.e. each Catalan number is the *gap* between the central binomial coefficient and its
immediate neighbour. Mathlib has the division form `catalan n = centralBinom n / (n+1)`
(`Nat.catalan_eq_centralBinom_div`) but not this subtraction-free-of-division form.

* `choose_two_mul_succ` — the neighbour coefficient is `C(2n,n+1) = n · catalan n`,
  obtained from the Pascal recurrence `choose_succ_right_eq` and
  `succ_mul_catalan_eq_centralBinom`.
* `catalan_eq_choose_sub` — the headline `catalan n = C(2n,n) − C(2n,n+1)`, since
  `C(2n,n) = (n+1)·catalan n` and `C(2n,n+1) = n·catalan n`, whose difference is
  `catalan n` (a genuine ℕ subtraction, never truncated).
* `catalan_eq_choose_sub_symm` — the reflected form `catalan (n+1) = C(2(n+1),n+1) −
  C(2(n+1),n)`, using the symmetry `C(2(n+1),n+2) = C(2(n+1),n)`; this is the ballot-number
  reading the open question asks for.

0 sorries, 0 axioms.
-/

import Mathlib

namespace CatalanNumbersOQ05OQ01

open Nat

/-- The off-centre central-binomial neighbour is `C(2n, n+1) = n · catalan n`. Derived
from the Pascal step `C(2n,n+1)·(n+1) = C(2n,n)·n` together with
`C(2n,n) = (n+1)·catalan n`. -/
theorem choose_two_mul_succ (n : ℕ) : (2 * n).choose (n + 1) = n * catalan n := by
  -- Pascal: C(2n, n+1)·(n+1) = C(2n, n)·(2n − n) = C(2n, n)·n.
  have hkey : (2 * n).choose (n + 1) * (n + 1) = (2 * n).choose n * n := by
    have h := Nat.choose_succ_right_eq (2 * n) n
    simpa [two_mul, Nat.add_sub_cancel] using h
  -- Central binomial in terms of the Catalan number.
  have hcb : (2 * n).choose n = (n + 1) * catalan n := by
    have h := succ_mul_catalan_eq_centralBinom n
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    omega
  -- Cancel the common factor (n+1).
  have heq : (2 * n).choose (n + 1) * (n + 1) = (n * catalan n) * (n + 1) := by
    rw [hkey, hcb]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) heq

/-- **Catalan number as a difference of central binomial coefficients.**
`catalan n = C(2n, n) − C(2n, n+1)`: each Catalan number is the gap between the central
binomial coefficient and its neighbour (the base, `k = 0`, ballot number). -/
theorem catalan_eq_choose_sub (n : ℕ) :
    catalan n = (2 * n).choose n - (2 * n).choose (n + 1) := by
  have hcb : (2 * n).choose n = (n + 1) * catalan n := by
    have h := succ_mul_catalan_eq_centralBinom n
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    omega
  rw [hcb, choose_two_mul_succ]
  have h : (n + 1) * catalan n = n * catalan n + catalan n := by ring
  omega

/-- **Reflected (ballot-number) form.** For `n ≥ 1` (here written `n+1`),
`catalan (n+1) = C(2(n+1), n+1) − C(2(n+1), n)`, using the binomial symmetry
`C(2(n+1), n+2) = C(2(n+1), n)`. This is the row-difference reading of the open question:
the Catalan number is the difference of two adjacent entries in row `2(n+1)` of Pascal's
triangle, read symmetrically about the centre. (The index `n+1` avoids the spurious ℕ
truncation `n−1` at `n=0`, where the unshifted reflected form would fail.) -/
theorem catalan_eq_choose_sub_symm (n : ℕ) :
    catalan (n + 1) = (2 * (n + 1)).choose (n + 1) - (2 * (n + 1)).choose n := by
  have hsymm : (2 * (n + 1)).choose ((n + 1) + 1) = (2 * (n + 1)).choose n := by
    have hle : (n + 1) + 1 ≤ 2 * (n + 1) := by omega
    have h := Nat.choose_symm hle
    have he : 2 * (n + 1) - ((n + 1) + 1) = n := by omega
    rw [he] at h
    exact h.symm
  rw [catalan_eq_choose_sub, hsymm]

end CatalanNumbersOQ05OQ01
