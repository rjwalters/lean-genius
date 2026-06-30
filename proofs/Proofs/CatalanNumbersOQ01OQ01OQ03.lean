import Mathlib

/-
# Catalan Numbers: closed forms for the central-binomial neighbours

Open Question (`catalan-numbers-oq-01-oq-01-oq-03`, child of the reflection-form
entry `catalan-numbers-oq-01-oq-01`).  The parent
(`CatalanReflectionFormOQ01`) records the classical *reflection* identity

  `catalan n = C(2n, n) − C(2n, n + 1)`,    i.e.    `C(2n, n) = catalan n + C(2n, n + 1)`,

splitting the central binomial coefficient `B = C(2n, n)` as the Catalan number
`C = catalan n` plus its immediate right neighbour `R = C(2n, n + 1)`.  That proof
used the auxiliary relation `(n + 1) · R = n · B` as a *step*, but never recorded
the resulting **closed form** of the neighbour itself.

This entry sharpens the reflection form into exact closed forms: every binomial
coefficient *adjacent* to the centre of row `2n` is an explicit multiple of the
Catalan number.

  * `C(2n, n + 1) = n · catalan n`            (the right neighbour, the main result),
  * `C(2n, n − 1) = n · catalan n`            (the left neighbour, by the row symmetry),
  * `(n + 2) · C(2n, n + 2) = n(n − 1) · catalan n`   (the second neighbour).

Combinatorially: of the `C(2n, n)` central lattice paths, the `catalan n` Dyck
paths sit at the centre, and each of the two flanking columns holds exactly
`n · catalan n` of the remaining paths — the reflection principle counts them.
The closed form `R = n · catalan n` makes the *strict* gap `R < B` transparent and
recovers `(n + 1) · catalan n = centralBinom n` as the simple consequence
`B = C + R = catalan n + n · catalan n`.

Everything is over `ℕ`, fully machine-checked, `0` axioms.  We use only Mathlib's
`succ_mul_catalan_eq_centralBinom`, the binomial step `Nat.choose_succ_right_eq`,
and the row symmetry `Nat.choose_symm`.

## Main results

* `choose_central_succ`        : `C(2n, n + 1) = n · catalan n`.
* `choose_central_pred`        : `C(2n, n − 1) = n · catalan n` (for `n ≥ 1`).
* `succ_mul_choose_central_succ` : `(n + 1) · C(2n, n + 1) = n · centralBinom n`.
* `choose_central_succ_two`    : `(n + 2) · C(2n, n + 2) = n(n − 1) · catalan n`.
* `choose_central_succ_lt`     : `C(2n, n + 1) < C(2n, n)` (the strict reflection gap).
* `centralBinom_eq_catalan_add_choose` : recovers the parent's additive split.
-/

namespace CatalanNumbersOQ01OQ01OQ03

open Nat

/-- The central binomial coefficient equals `(n + 1) · catalan n`, phrased with the
explicit `(2 * n).choose n` (definitionally Mathlib's `centralBinom n`). -/
private theorem choose_central (n : ℕ) : (2 * n).choose n = (n + 1) * catalan n :=
  (succ_mul_catalan_eq_centralBinom n).symm

/-- **Right neighbour of the central binomial coefficient.**

  `C(2n, n + 1) = n · catalan n`.

The immediate right neighbour of the central coefficient is exactly `n` times the
`n`-th Catalan number.  This is the closed form behind the parent's reflection
identity: the auxiliary relation `(n + 1) · C(2n, n+1) = n · C(2n, n)` is solved for
`C(2n, n+1)` using `C(2n, n) = (n + 1) · catalan n`. -/
theorem choose_central_succ (n : ℕ) :
    (2 * n).choose (n + 1) = n * catalan n := by
  -- Neighbour relation `(n + 1) · R = n · B`, from `Nat.choose_succ_right_eq`.
  have hstep : (n + 1) * ((2 * n).choose (n + 1)) = n * ((2 * n).choose n) := by
    have h := Nat.choose_succ_right_eq (2 * n) n
    have e : 2 * n - n = n := by omega
    rw [e] at h
    calc (n + 1) * ((2 * n).choose (n + 1))
          = (2 * n).choose (n + 1) * (n + 1) := by ring
      _ = (2 * n).choose n * n := h
      _ = n * ((2 * n).choose n) := by ring
  -- Cancel the positive factor `n + 1` after substituting `B = (n + 1) · catalan n`.
  have hmul : (n + 1) * ((2 * n).choose (n + 1)) = (n + 1) * (n * catalan n) := by
    rw [hstep, choose_central]; ring
  exact Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega) hmul

/-- **Left neighbour of the central binomial coefficient.**

  `C(2n, n − 1) = n · catalan n`    (for `n ≥ 1`).

By the symmetry of row `2n` the left neighbour equals the right neighbour, hence
the same closed form. -/
theorem choose_central_pred (n : ℕ) (hn : 1 ≤ n) :
    (2 * n).choose (n - 1) = n * catalan n := by
  have hsymm : (2 * n).choose (n - 1) = (2 * n).choose (n + 1) := by
    have e : 2 * n - (n + 1) = n - 1 := by omega
    rw [← e, Nat.choose_symm (by omega)]
  rw [hsymm, choose_central_succ]

/-- **Multiplicative form of the right-neighbour identity.**

  `(n + 1) · C(2n, n + 1) = n · centralBinom n`.

The neighbour is to the centre as `n` is to `n + 1`. -/
theorem succ_mul_choose_central_succ (n : ℕ) :
    (n + 1) * (2 * n).choose (n + 1) = n * Nat.centralBinom n := by
  rw [choose_central_succ, show Nat.centralBinom n = (2 * n).choose n from rfl,
      choose_central]
  ring

/-- **Second right neighbour.**

  `(n + 2) · C(2n, n + 2) = n · (n − 1) · catalan n`.

Iterating the binomial step once more past the right neighbour `C(2n, n + 1)`. -/
theorem choose_central_succ_two (n : ℕ) :
    (n + 2) * (2 * n).choose (n + 2) = n * (n - 1) * catalan n := by
  have h := Nat.choose_succ_right_eq (2 * n) (n + 1)
  -- h : (2*n).choose (n + 1 + 1) * (n + 1 + 1) = (2*n).choose (n + 1) * (2*n - (n + 1))
  rw [choose_central_succ] at h
  have e : 2 * n - (n + 1) = n - 1 := by omega
  rw [e] at h
  -- h : (2*n).choose (n + 2) * (n + 2) = n * catalan n * (n - 1)
  calc (n + 2) * (2 * n).choose (n + 2)
        = (2 * n).choose (n + 2) * (n + 2) := by ring
    _ = n * catalan n * (n - 1) := h
    _ = n * (n - 1) * catalan n := by ring

/-- The Catalan number is strictly positive (every row of `2n` has at least one
Dyck path). -/
private theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · exfalso
    have h := succ_mul_catalan_eq_centralBinom n
    rw [h0, Nat.mul_zero] at h
    exact (Nat.centralBinom_pos n).ne h
  · exact h0

/-- **Strict reflection gap.**

  `C(2n, n + 1) < C(2n, n)`.

The right neighbour is strictly below the central coefficient (their difference is
the positive number `catalan n`), so the `ℕ`-subtraction in the parent's reflection
form is a genuine difference, never truncated. -/
theorem choose_central_succ_lt (n : ℕ) :
    (2 * n).choose (n + 1) < (2 * n).choose n := by
  rw [choose_central_succ, choose_central]
  have hpos := catalan_pos n
  nlinarith [hpos]

/-- **Recovering the parent's additive reflection split** from the closed form:

  `C(2n, n) = catalan n + C(2n, n + 1)`. -/
theorem centralBinom_eq_catalan_add_choose (n : ℕ) :
    (2 * n).choose n = catalan n + (2 * n).choose (n + 1) := by
  rw [choose_central, choose_central_succ]; ring

/-- Sanity check (`n = 4`): `C(8, 5) = 56 = 4 · 14 = 4 · catalan 4`. -/
example : (2 * 4).choose (4 + 1) = 4 * catalan 4 := choose_central_succ 4

/-- `C(8, 5) = 56 = 4 · 14`. -/
example : Nat.choose 8 5 = 4 * 14 := by decide

/-- Second neighbour at `n = 4`: `(4 + 2) · C(8, 6) = 4 · 3 · catalan 4`, i.e.
`6 · 28 = 12 · 14 = 168`. -/
example : Nat.choose 8 6 * 6 = 4 * 3 * 14 := by decide

end CatalanNumbersOQ01OQ01OQ03
