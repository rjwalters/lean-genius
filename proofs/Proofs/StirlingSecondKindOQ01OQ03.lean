/-
Stirling Numbers of the Second Kind — OQ-01-OQ-03:
the second subdiagonal closed form

  S(m+2, m) = C(m+2, 3) + 3·C(m+2, 4).

Source: Open question OQ-03 of the gallery entry `stirling-second-kind-oq-01`
(itself OQ-01 of the parent `stirling-second-kind`).

## The open question

Mathlib (`Mathlib/Combinatorics/Enumerative/Stirling.lean`) records the Pascal-style
recurrence `S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)`, the diagonal `S(n,n) = 1`, and the
**first subdiagonal** `S(n+1,n) = C(n+1,2)` (`Nat.stirlingSecond_succ_self_left`).
It does **not** record the **second subdiagonal**

  S(n, n−2) = C(n,3) + 3·C(n,4)        (n ≥ 2),

equivalently `S(m+2, m) = C(m+2,3) + 3·C(m+2,4)`.  Combinatorially this counts the
partitions of an `(m+2)`-element set into `m` blocks: such a partition either has one
block of size three and the rest singletons (`C(m+2,3)` ways), or two blocks of size
two and the rest singletons (`3·C(m+2,4)` ways — choose the four non-singleton elements
and pair them in one of `3` ways).  This file proves the identity directly from the
Mathlib recurrence, by induction on `m`.

## Strategy — telescoping the Pascal recurrence along the diagonal

Fix the claim `P(m) : S(m+2, m) = C(m+2,3) + 3·C(m+2,4)` and induct on `m`.

The successor step uses the recurrence once, with `n = m+2`, `k = m`:

  S(m+3, m+1) = (m+1)·S(m+2, m+1) + S(m+2, m).

The first summand is `(m+1)·C(m+2,2)` by the **first subdiagonal**
(`stirlingSecond_succ_self_left`), and the second is the induction hypothesis.
Two applications of **Pascal's rule** `C(n+1,k+1) = C(n,k) + C(n,k+1)` rewrite the
target `C(m+3,3) + 3·C(m+3,4)` over the column `n = m+2`, after which the whole step
reduces to the single **absorption identity**

  m·C(m+2,2) = 3·C(m+2,3),

itself an instance of `Nat.choose_succ_right_eq` (`C(n,k+1)·(k+1) = C(n,k)·(n−k)` at
`n = m+2, k = 2`).  All arithmetic stays in `ℕ`.
-/
import Mathlib

namespace StirlingSecondKindOQ01OQ03

open Nat

/-- **Absorption identity** `m·C(m+2,2) = 3·C(m+2,3)`, the single non-`omega` fact behind
the induction step.  It is the `n = m+2, k = 2` case of `Nat.choose_succ_right_eq`. -/
theorem absorption (m : ℕ) : m * (m + 2).choose 2 = 3 * (m + 2).choose 3 := by
  have h := Nat.choose_succ_right_eq (m + 2) 2
  -- h : (m+2).choose 3 * 3 = (m+2).choose 2 * ((m+2) - 2)
  rw [Nat.add_sub_cancel] at h
  rw [mul_comm m, mul_comm 3]
  exact h.symm

/-- **Second subdiagonal of the Stirling numbers of the second kind.**

  `S(m+2, m) = C(m+2, 3) + 3·C(m+2, 4)`.

Proved by induction on `m` from the Mathlib Pascal recurrence
`stirlingSecond_succ_succ`, the first subdiagonal `stirlingSecond_succ_self_left`,
two instances of Pascal's rule, and `absorption`. -/
theorem stirlingSecond_sub_two (m : ℕ) :
    Nat.stirlingSecond (m + 2) m = (m + 2).choose 3 + 3 * (m + 2).choose 4 := by
  induction m with
  | zero => decide
  | succ m ih =>
    -- S(m+3, m+1) = (m+1)·S(m+2, m+1) + S(m+2, m)
    have step : Nat.stirlingSecond (m + 1 + 2) (m + 1)
        = (m + 1) * Nat.stirlingSecond (m + 2) (m + 1) + Nat.stirlingSecond (m + 2) m :=
      Nat.stirlingSecond_succ_succ (m + 2) m
    -- first subdiagonal: S(m+2, m+1) = C(m+2, 2)
    have sub1 : Nat.stirlingSecond (m + 2) (m + 1) = (m + 2).choose 2 :=
      Nat.stirlingSecond_succ_self_left (m + 1)
    -- Pascal's rule on the target column n = m+2
    have p3 : (m + 1 + 2).choose 3 = (m + 2).choose 2 + (m + 2).choose 3 :=
      Nat.choose_succ_succ' (m + 2) 2
    have p4 : (m + 1 + 2).choose 4 = (m + 2).choose 3 + (m + 2).choose 4 :=
      Nat.choose_succ_succ' (m + 2) 3
    rw [step, sub1, ih, p3, p4, add_one_mul, absorption]
    omega

/-- Equivalent statement on `n ≥ 2`: `S(n, n−2) = C(n,3) + 3·C(n,4)`. -/
theorem stirlingSecond_sub_two' (n : ℕ) (hn : 2 ≤ n) :
    Nat.stirlingSecond n (n - 2) = n.choose 3 + 3 * n.choose 4 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, Nat.add_sub_cancel] using stirlingSecond_sub_two m

/-- Sanity checks against directly computed values. -/
example : Nat.stirlingSecond 2 0 = 0 := by decide
example : Nat.stirlingSecond 3 1 = 1 := by decide
example : Nat.stirlingSecond 4 2 = 7 := by decide
example : Nat.stirlingSecond 5 3 = 25 := by decide
example : Nat.stirlingSecond 6 4 = 65 := by decide

end StirlingSecondKindOQ01OQ03
