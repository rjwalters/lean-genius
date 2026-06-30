import Proofs.BallotProblemOQ04

/-!
# The First Crossing Partition: the `n = 4` Discriminator (oq-04-oq-01)

The parent entry `ballot-problem-oq-04` (Non-Crossing Partitions) formalizes the
predicate `IsNonCrossing` on `Setoid (Fin n)` and proves every partition of `Fin n`
with `n ≤ 3` is non-crossing (`isNonCrossing_of_n_le_three`). Its open questions
(#1, #2) note that the non-crossing count first *discriminates* from the Bell number
at `n = 4`: of the `B₄ = 15` partitions of a 4-element set, exactly one is a genuine
crossing, leaving `catalan 4 = 14` non-crossing ones.

This file exhibits that unique crossing partition explicitly and proves it crosses,
giving the `n = 4` discriminator a concrete, verified witness (0 `sorry`, 0 `axiom`).

The crossing partition `{{0, 2}, {1, 3}}` of `Fin 4` is exactly the **same-parity**
equivalence relation: `0, 2` are the even points and `1, 3` the odd points. Its two
blocks interleave — `0 < 1 < 2 < 3` with `0 ~ 2` and `1 ~ 3` but `¬ 0 ~ 1` — which
is precisely the forbidden configuration of `IsNonCrossing`.
-/

namespace BallotProblemOQ04OQ01

open BallotProblemOQ04

/-- The crossing partition `{{0, 2}, {1, 3}}` of `Fin 4`, realized as the same-parity
equivalence relation (the kernel of the parity map `x ↦ x.val % 2`). Its even block is
`{0, 2}` and its odd block is `{1, 3}`. -/
def crossing4 : Setoid (Fin 4) := Setoid.ker (fun x => x.val % 2)

/-- Membership in `crossing4` is having the same parity. -/
theorem crossing4_iff (x y : Fin 4) : crossing4 x y ↔ x.val % 2 = y.val % 2 := Iff.rfl

/-- The two blocks of `crossing4` are `{0, 2}` (even) and `{1, 3}` (odd): the outer
pair `0 ~ 2` and the inner pair `1 ~ 3` are each related, but they are different
blocks (`¬ 0 ~ 1`). This is the interleaving that makes the partition cross. -/
theorem crossing4_blocks :
    crossing4 0 2 ∧ crossing4 1 3 ∧ ¬ crossing4 0 1 :=
  ⟨(show (0 : Fin 4).val % 2 = (2 : Fin 4).val % 2 by decide),
   (show (1 : Fin 4).val % 2 = (3 : Fin 4).val % 2 by decide),
   (show ¬ ((0 : Fin 4).val % 2 = (1 : Fin 4).val % 2) by decide)⟩

/-- **The `n = 4` discriminator.** The same-parity partition `{{0, 2}, {1, 3}}` of
`Fin 4` is *not* non-crossing: it is the first genuine crossing, the single partition
separating `B₄ = 15` from `catalan 4 = 14`. -/
theorem not_isNonCrossing_crossing4 : ¬ IsNonCrossing crossing4 := by
  intro h
  obtain ⟨h02, h13, h01⟩ := crossing4_blocks
  exact h01 (h 0 1 2 3 (by decide) (by decide) (by decide) h02 h13)

/-- Restated through the parent's "no genuine crossing" reformulation
`isNonCrossing_iff`: `crossing4` *does* contain a forbidden interleaving quadruple
`0 < 1 < 2 < 3` with `0 ~ 2`, `1 ~ 3`, `¬ 0 ~ 1`. -/
theorem crossing4_has_crossing :
    ∃ a b c d : Fin 4, a < b ∧ b < c ∧ c < d ∧ crossing4 a c ∧ crossing4 b d ∧
      ¬ crossing4 a b := by
  obtain ⟨h02, h13, h01⟩ := crossing4_blocks
  exact ⟨0, 1, 2, 3, by decide, by decide, by decide, h02, h13, h01⟩

end BallotProblemOQ04OQ01
