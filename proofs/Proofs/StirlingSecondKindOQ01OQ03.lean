/-
Stirling Numbers of the Second Kind — OQ-01-OQ-03:
the second subdiagonal closed form

  S(m+2, m) = C(m+2, 3) + 3·C(m+2, 4),

equivalently  S(n, n−2) = C(n,3) + 3·C(n,4)  for n ≥ 2.

Source: Open question OQ-03 of the gallery entry `stirling-second-kind-oq-01`
(itself OQ-01 of the parent `stirling-second-kind`).

## The open question

Mathlib (`Mathlib/Combinatorics/Enumerative/Stirling.lean`) records the Pascal-style
recurrence for `Nat.stirlingSecond`, the value on the diagonal
`stirlingSecond_self : S(n,n) = 1`, and the **first subdiagonal**
`stirlingSecond_succ_self_left : S(n+1,n) = C(n+1,2)`.  It stops there: the next
diagonal `S(n, n−2)` has no closed form in Mathlib.  This file supplies it.

## The formula and a sanity check

The classical second-subdiagonal value is

  S(n, n−2) = C(n,3) + 3·C(n,4).

Reindexed by `n = m+2` this is `S(m+2,m) = C(m+2,3) + 3·C(m+2,4)`, valid for all
`m : ℕ` (both sides are `0` at `m = 0`, since `S(2,0)=0` and `C(2,3)=C(2,4)=0`).
Numeric checks: `S(4,2)=7 = C(4,3)+3C(4,4) = 4+3`; `S(5,3)=25 = C(5,3)+3C(5,4) =
10+15`; `S(6,4)=65 = C(6,3)+3C(6,4) = 20+45`.

## Strategy — induction on m off the first subdiagonal

Apply the Pascal recurrence `S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)` with
`n = m+2`, `k = m`:

  S(m+3, m+1) = (m+1)·S(m+2, m+1) + S(m+2, m).

Here `S(m+2, m+1)` is the **first subdiagonal** `C(m+2,2)` (Mathlib's
`stirlingSecond_succ_self_left`), and `S(m+2, m)` is the induction hypothesis.  The
inductive step then reduces to a pure binomial identity, whose only nontrivial input
is the **absorption identity**

  3·C(m+2, 3) = m·C(m+2, 2),

an instance of `Nat.choose_succ_right_eq`.  Two applications of Pascal's rule on the
target binomials `C(m+3,3)`, `C(m+3,4)` then make both sides agree by `ring`.
-/
import Mathlib

namespace StirlingSecondKindOQ01OQ03

open Nat

/-- **Absorption identity** specialised to the third column:
`3·C(m+2, 3) = m·C(m+2, 2)`.  This is `Nat.choose_succ_right_eq (m+2) 2`, namely
`C(m+2,3)·3 = C(m+2,2)·(m+2−2)`, after simplifying `m+2−2 = m`. -/
theorem three_mul_choose_three (m : ℕ) :
    (m + 2).choose 3 * 3 = (m + 2).choose 2 * m := by
  have h := Nat.choose_succ_right_eq (m + 2) 2
  simpa using h

/-- **Main theorem — the second subdiagonal of the Stirling triangle.**

For all `m : ℕ`,

  `S(m+2, m) = C(m+2, 3) + 3·C(m+2, 4)`.

Proved by induction on `m`, stepping down the diagonal via the Pascal recurrence and
the first-subdiagonal value `S(m+2,m+1) = C(m+2,2)`. -/
theorem stirlingSecond_add_two_sub_two (m : ℕ) :
    Nat.stirlingSecond (m + 2) m = (m + 2).choose 3 + 3 * (m + 2).choose 4 := by
  induction m with
  | zero =>
    -- S(2,0) = 0 and C(2,3) + 3·C(2,4) = 0 + 0.
    decide
  | succ m ih =>
    -- Pascal recurrence with n = m+2, k = m :
    --   S(m+3, m+1) = (m+1)·S(m+2, m+1) + S(m+2, m).
    have key : Nat.stirlingSecond (m + 3) (m + 1)
        = (m + 1) * Nat.stirlingSecond (m + 2) (m + 1) + Nat.stirlingSecond (m + 2) m :=
      Nat.stirlingSecond_succ_succ (m + 2) m
    -- First subdiagonal: S(m+2, m+1) = C(m+2, 2).
    have hsub : Nat.stirlingSecond (m + 2) (m + 1) = (m + 2).choose 2 :=
      Nat.stirlingSecond_succ_self_left (m + 1)
    -- Pascal's rule on the two target binomials.
    have p1 : (m + 3).choose 3 = (m + 2).choose 2 + (m + 2).choose 3 :=
      Nat.choose_succ_succ (m + 2) 2
    have p2 : (m + 3).choose 4 = (m + 2).choose 3 + (m + 2).choose 4 :=
      Nat.choose_succ_succ (m + 2) 3
    -- Absorption identity, cast to ℤ for the final `linear_combination`.
    have haZ : ((m + 2).choose 3 : ℤ) * 3 = ((m + 2).choose 2 : ℤ) * m := by
      exact_mod_cast three_mul_choose_three m
    show Nat.stirlingSecond (m + 3) (m + 1)
        = (m + 3).choose 3 + 3 * (m + 3).choose 4
    rw [key, hsub, ih, p1, p2]
    zify
    linear_combination -haZ

/-- **Subdiagonal restatement.**  For `n ≥ 2`,
`S(n, n−2) = C(n,3) + 3·C(n,4)`. -/
theorem stirlingSecond_sub_two {n : ℕ} (hn : 2 ≤ n) :
    Nat.stirlingSecond n (n - 2) = n.choose 3 + 3 * n.choose 4 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- n = 2 + m ; rewrite to m + 2 and apply the main theorem.
  have hm : 2 + m - 2 = m := by omega
  rw [hm, show 2 + m = m + 2 from by ring]
  exact stirlingSecond_add_two_sub_two m

/-- Sanity check: `S(4,2) = 7`. -/
theorem stirlingSecond_four_two : Nat.stirlingSecond 4 2 = 7 := by decide

/-- Sanity check: `S(5,3) = 25`. -/
theorem stirlingSecond_five_three : Nat.stirlingSecond 5 3 = 25 := by decide

/-- Sanity check: `S(6,4) = 65`. -/
theorem stirlingSecond_six_four : Nat.stirlingSecond 6 4 = 65 := by decide

end StirlingSecondKindOQ01OQ03
