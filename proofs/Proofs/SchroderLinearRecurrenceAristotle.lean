import Mathlib.Combinatorics.Enumerative.Schroder
import Mathlib.Tactic

/-
# Companion file: the order-two holonomic recurrence for large Schröder numbers

This file isolates the HARD (but classical) result for automated proof search.

The headline recurrence `largeSchroder_holonomic` is now proved *unconditionally on top of*
the single convolution lemma `largeSchroder_conv_holonomic` (the reduction is a routine
`linear_combination`, recorded below).  Hence the **only** remaining `sorry` — the sole piece
needing generating-function / creative-telescoping machinery — is `largeSchroder_conv_holonomic`.

The large Schröder numbers `L = Nat.largeSchroder` satisfy the order-two holonomic
(P-recursive) linear recurrence

  `(n + 3) * L (n+2) + n * L n = 3 * (2n + 3) * L (n+1)`,

equivalently `(n+1) * L n = 3 * (2n-1) * L (n-1) - (n-2) * L (n-2)` for `n ≥ 2`.
Values: L 0 = 1, L 1 = 2, L 2 = 6, L 3 = 22, L 4 = 90, L 5 = 394.

## Proof sketch (generating functions)

Let `f = ∑ L n xⁿ`.  The convolution recurrence `Nat.largeSchroder_succ` translates to the
algebraic equation `x * f^2 + (x - 1) * f + 1 = 0`.  Differentiating and eliminating `f^2`
and `f * f'` gives the linear ODE `x * (x^2 - 6x + 1) * f' = (3x - 1) * f + (x + 1)`, whose
`xⁿ`-coefficient is exactly the stated recurrence.

## Equivalent convolution form (a useful intermediate)

Writing `Q n = ∑ i ≤ n, L i * L (n - i)` for the convolution (so `L (n+1) = L n + Q n`), the
recurrence is equivalent to

  `(n + 3) * Q (n+1) = (5n + 6) * Q n + (4n + 6) * L n`.

Both statements below are over `ℕ` with no subtraction.
-/

namespace Nat

open Finset

/-- Convolution-form reformulation of the holonomic recurrence (see module docstring). -/
theorem largeSchroder_conv_holonomic (n : ℕ) :
    (n + 3) * (∑ i ≤ n + 1, largeSchroder i * largeSchroder (n + 1 - i))
      = (5 * n + 6) * (∑ i ≤ n, largeSchroder i * largeSchroder (n - i))
        + (4 * n + 6) * largeSchroder n := by
  sorry

/-- **Order-two holonomic recurrence for the large Schröder numbers.**
`(n + 3) * L (n+2) + n * L n = 3 * (2n + 3) * L (n+1)`.

This is a *mechanical consequence* of the convolution-form recurrence
`largeSchroder_conv_holonomic` together with the defining quadratic recurrence
`Nat.largeSchroder_succ` (which gives `L (n+1) = L n + Q n` and
`L (n+2) = L (n+1) + Q (n+1)`).  Substituting both and eliminating the
convolution sum `Q (n+1)` via the convolution form leaves a linear identity
in `L n`, `Q n`, `Q (n+1)` that `linear_combination` discharges.  Thus the
only genuinely hard content is `largeSchroder_conv_holonomic`. -/
theorem largeSchroder_holonomic (n : ℕ) :
    (n + 3) * largeSchroder (n + 2) + n * largeSchroder n
      = 3 * (2 * n + 3) * largeSchroder (n + 1) := by
  have hconv := largeSchroder_conv_holonomic n
  rw [largeSchroder_succ (n + 1), largeSchroder_succ n]
  -- After the two rewrites, both the goal and `hconv` are expressed in `largeSchroder n`
  -- and the two convolution sums `Q n` and `Q (n+1)`; abstract the latter so the remaining
  -- step is a pure linear identity.
  set S := ∑ i ≤ n, largeSchroder i * largeSchroder (n - i)
  set T := ∑ i ≤ n + 1, largeSchroder i * largeSchroder (n + 1 - i)
  zify at hconv ⊢
  linear_combination hconv

end Nat
