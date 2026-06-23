/-
  Ballot Problem — OQ-01-OQ-03: The Catalan number as a ballot/reflection count

  The classical ballot theorem is proved by the *reflection principle*: the
  number of "good" lattice paths (those that stay strictly on one side) equals
  the total number of paths minus the number of "bad" paths, where the bad paths
  are counted bijectively by reflecting them.  For the symmetric Dyck-path case
  (n up-steps, n down-steps, never dipping below the axis) this reflection count
  is

      catalan n = C(2n, n) − C(2n, n+1).

  This is the *reflection form* of the Catalan number.  It is mathematically
  distinct from Mathlib's *division form*
      `catalan_eq_centralBinom_div : catalan n = centralBinom n / (n + 1)`
  in that it never divides: it is a literal "all paths minus reflected bad paths"
  difference, which is exactly what the ballot/reflection argument produces.

  The two forms are reconciled here in `choose_sub_choose_eq_centralBinom_div`.

  Key Mathlib inputs (all from `import Mathlib`):
  * `Nat.choose_succ_right_eq`           — adjacent-binomial recurrence
  * `Nat.centralBinom_eq_two_mul_choose` — centralBinom n = (2n).choose n
  * `succ_mul_catalan_eq_centralBinom` — (n+1) * catalan n = centralBinom n
  * `catalan_eq_centralBinom_div`    — division form (for reconciliation)

  Reference: https://erdosproblems.com (ballot problem family); reflection
  principle / Catalan numbers, standard.
-/

import Mathlib

namespace BallotProblemOQ01OQ03

open Nat

/--
**Central binomial in terms of the Catalan number** (a convenient repackaging of
`succ_mul_catalan_eq_centralBinom`): the central binomial coefficient
`(2n).choose n` is `(n+1)` copies of `catalan n`.
-/
theorem two_mul_choose_eq (n : ℕ) :
    (2 * n).choose n = (n + 1) * catalan n := by
  rw [← Nat.centralBinom_eq_two_mul_choose, succ_mul_catalan_eq_centralBinom]

/--
**The "one-off" binomial is `n` copies of the Catalan number.**

`(2n).choose (n+1) = n · catalan n`.  This is the count of *bad* (reflected)
Dyck paths in the reflection argument.  Proved from the adjacent-binomial
recurrence `choose_succ_right_eq` by cancelling the factor `(n+1)`.
-/
theorem two_mul_choose_succ_eq (n : ℕ) :
    (2 * n).choose (n + 1) = n * catalan n := by
  have h := Nat.choose_succ_right_eq (2 * n) n
  rw [two_mul_choose_eq] at h
  have h2n : 2 * n - n = n := by omega
  rw [h2n] at h
  -- h : (2*n).choose (n+1) * (n+1) = (n+1) * catalan n * n
  have hcancel :
      (2 * n).choose (n + 1) * (n + 1) = (n * catalan n) * (n + 1) := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) hcancel

/--
**Reflection form of the Catalan number (ballot count).**

    catalan n = C(2n, n) − C(2n, n+1).

The right-hand side is exactly "(all monotone lattice paths) − (reflected bad
paths)", the quantity the reflection principle delivers for the ballot theorem.
No division is involved, in contrast to `catalan_eq_centralBinom_div`.
-/
theorem catalan_eq_choose_sub_choose (n : ℕ) :
    catalan n = (2 * n).choose n - (2 * n).choose (n + 1) := by
  rw [two_mul_choose_eq, two_mul_choose_succ_eq, add_one_mul]
  -- goal: catalan n = n * catalan n + catalan n - n * catalan n
  omega

/--
**Reconciliation of the reflection form with Mathlib's division form.**

    C(2n, n) − C(2n, n+1) = centralBinom n / (n + 1).

Both compute `catalan n`; this confirms the ballot/reflection count agrees with
the standard closed form.
-/
theorem choose_sub_choose_eq_centralBinom_div (n : ℕ) :
    (2 * n).choose n - (2 * n).choose (n + 1) = n.centralBinom / (n + 1) := by
  rw [← catalan_eq_choose_sub_choose, catalan_eq_centralBinom_div]

end BallotProblemOQ01OQ03
