/-
  The derangement quotient sequence q(n) = D(n)/(n−1) is OEIS A000255
  Open Question: derangements-convergence-oq-04-oq-01

  The parent entry (derangements-convergence-oq-04) proved that for every
  n ≥ 2 the number of derangements D(n) = numDerangements n is divisible by
  n − 1, via the additive recurrence

    D(n) = (n − 1) · (D(n−2) + D(n−1))            (numDerangements_add_two).

  This child studies the resulting integer quotient

    q(n) = D(n) / (n − 1) = D(n−2) + D(n−1),

  which the parent's open question asked us to identify and give a closed
  recurrence for.

  ## Main results

  Reindexing so the arithmetic is subtraction-free, we work with

    q m := numDerangements m + numDerangements (m + 1)          (= q(m+2) above).

  * `numDerangements_eq_sub_one_mul_q` : for n ≥ 2,
        D(n) = (n − 1) · q (n − 2),
    i.e. `q (n−2)` really is the integer quotient `D(n)/(n−1)`.

  * `q_add_two` : the sequence satisfies the second-order recurrence
        q(m+2) = (m+2) · q(m+1) + (m+1) · q(m).
    Together with q 0 = q 1 = 1 this is exactly the defining recurrence of
    **OEIS A000255** (a(n) = n·a(n−1) + (n−1)·a(n−2), a(0)=a(1)=1), whose first
    terms are 1, 1, 3, 11, 53, 309, …  A000255 counts the permutations of
    {0,…,m} that fix the point 0 and derange the rest — equivalently the
    permutations of an (m+1)-set with exactly one fixed point, divided by m+1.

  The recurrence for `q` is *not* a restatement of the derangement recurrence:
  it is obtained by expanding both `D(m+2)` and `D(m+3)` through
  `numDerangements_add_two` and recombining, so that the two consecutive
  derangement values reassemble into `q(m+1)` and `q(m)` with the polynomial
  coefficients `m+2` and `m+1`.

  Everything is machine-checked over `ℕ` with no additional axioms.
-/

import Mathlib

open Nat

namespace DerangementsConvergenceOQ04OQ01

/-- The derangement quotient sequence, reindexed to avoid subtraction:
    `q m = D(m) + D(m+1)`.  Under the parent's indexing this is
    `q(m+2) = D(m+2)/(m+1)`. -/
def q (m : ℕ) : ℕ := numDerangements m + numDerangements (m + 1)

/-- Unfolding lemma: `q m = D(m) + D(m+1)`. -/
theorem q_eq (m : ℕ) : q m = numDerangements m + numDerangements (m + 1) := rfl

/-- **`q` is the integer quotient `D(n)/(n−1)`.**  For every `n ≥ 2`,
    `D(n) = (n − 1) · q (n − 2)`.  Combined with the parent's divisibility
    result, this pins down `q (n−2) = D(n)/(n−1)`. -/
theorem numDerangements_eq_sub_one_mul_q (n : ℕ) (hn : 2 ≤ n) :
    numDerangements n = (n - 1) * q (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  show numDerangements (m + 2) = (m + 1) * q m
  simp only [q]
  rw [numDerangements_add_two]

/-- **Second-order recurrence for the quotient sequence (OEIS A000255).**
    `q(m+2) = (m+2) · q(m+1) + (m+1) · q(m)`.

    Proof: expand `D(m+2)` and `D(m+3)` by the additive derangement
    recurrence and regroup — the four consecutive derangement values
    reassemble into `q(m+1)` and `q(m)`. -/
theorem q_add_two (m : ℕ) :
    q (m + 2) = (m + 2) * q (m + 1) + (m + 1) * q m := by
  have hD2 : numDerangements (m + 2)
      = (m + 1) * (numDerangements m + numDerangements (m + 1)) := numDerangements_add_two m
  have hD3 : numDerangements (m + 3)
      = (m + 2) * (numDerangements (m + 1) + numDerangements (m + 2)) :=
    numDerangements_add_two (m + 1)
  show numDerangements (m + 2) + numDerangements (m + 3)
      = (m + 2) * (numDerangements (m + 1) + numDerangements (m + 2))
        + (m + 1) * (numDerangements m + numDerangements (m + 1))
  rw [hD3, hD2]
  ring

/-- Base value `q 0 = 1` (`= D(0) + D(1) = 1 + 0`). -/
theorem q_zero : q 0 = 1 := by decide

/-- Base value `q 1 = 1` (`= D(1) + D(2) = 0 + 1`). -/
theorem q_one : q 1 = 1 := by decide

-- First terms of A000255: 1, 1, 3, 11, 53, 309.
example : q 2 = 3 := by decide
example : q 3 = 11 := by decide
example : q 4 = 53 := by decide
example : q 5 = 309 := by decide

-- The recurrence reproduces the tabulated terms, e.g. q 4 = 4·q 3 + 3·q 2 = 44 + 9 = 53.
example : q 4 = 4 * q 3 + 3 * q 2 := q_add_two 2
-- and the quotient identity: D(6) = 5 · q 4 = 5 · 53 = 265.
example : numDerangements 6 = (6 - 1) * q (6 - 2) := numDerangements_eq_sub_one_mul_q 6 (by norm_num)

-- Axiom audit: both headline theorems must depend only on foundational axioms
-- (propext / Classical.choice / Quot.sound) — no sorryAx, no Lean.ofReduceBool.
#print axioms numDerangements_eq_sub_one_mul_q
#print axioms q_add_two

end DerangementsConvergenceOQ04OQ01
