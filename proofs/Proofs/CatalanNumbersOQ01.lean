import Mathlib

/-!
# Catalan Numbers: the O(1) Linear Recurrence

Mathlib (`Mathlib/Combinatorics/Enumerative/Catalan.lean`) provides the Catalan
numbers `catalan` together with the quadratic **Segner convolution recurrence**
`catalan_succ'` and the closed form `catalan_eq_centralBinom_div`.  It does *not*
state the first-order ("holonomic") **linear recurrence**

  `(n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n`,

which computes `catalan (n + 1)` from `catalan n` in `O(1)` arithmetic operations
rather than the `O(n)` Segner convolution sum.

We derive it from the central-binomial bridge.  Writing `C n` for `catalan n`
and `B n` for `Nat.centralBinom n`, Mathlib provides
* `succ_mul_catalan_eq_centralBinom : (n + 1) * C n = B n`, and
* `Nat.succ_mul_centralBinom_succ : (n + 1) * B (n + 1) = 2 * (2 * n + 1) * B n`.

Multiplying the target by `n + 1` and substituting both identities turns it into a
ring identity in the central binomial coefficients; cancelling the positive factor
`n + 1` gives the result.  Everything is over `ℕ`, fully machine-checked, 0-axiom.
-/

/-- **The linear (holonomic) recurrence for Catalan numbers.**
`(n + 2) · C(n+1) = 2·(2n+1) · C(n)`.  This is the first-order recurrence
satisfied by the Catalan numbers — strictly stronger as a *computational* tool
than the quadratic Segner convolution `catalan_succ'`, since it determines
`catalan (n + 1)` from the single previous value `catalan n`. -/
theorem catalan_linear_recurrence (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  -- Bridge to central binomial coefficients (`n + 1 + 1` is `n + 2` definitionally).
  have h1 : (n + 2) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 : (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom :=
    Nat.succ_mul_centralBinom_succ n
  have h3 : (n + 1) * catalan n = n.centralBinom :=
    succ_mul_catalan_eq_centralBinom n
  -- Prove the goal after multiplying through by the positive factor `n + 1`,
  -- then cancel it.
  refine Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega) ?_
  calc
    (n + 1) * ((n + 2) * catalan (n + 1))
        = (n + 1) * (n + 1).centralBinom := by rw [h1]
    _   = 2 * (2 * n + 1) * n.centralBinom := h2
    _   = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [h3]
    _   = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring

/-- The linear recurrence solved for the next Catalan number, exhibiting the
exact `O(1)` step `C(n+1) = 2·(2n+1)·C(n) / (n + 2)` over `ℕ` (the division is
exact because `n + 2` divides the left-hand side). -/
theorem catalan_succ_eq_div (n : ℕ) :
    catalan (n + 1) = 2 * (2 * n + 1) * catalan n / (n + 2) := by
  rw [← catalan_linear_recurrence, Nat.mul_div_cancel_left]
  omega

/-- Sanity check: the linear recurrence reproduces `catalan 4 = 14` from
`catalan 3 = 5` in one step. -/
example : catalan 4 = 14 := by
  have h := catalan_linear_recurrence 3
  norm_num [catalan_three] at h
  omega
