import Mathlib

/-
# Abel–Ruffini OQ-06 — companion: the remaining S₄ / A₄ case

The verified file `AbelRuffiniOQ06.lean` proves the reduction
`Aₙ solvable ⟹ Sₙ solvable` and settles `S₂`, `S₃`. The only symmetric group
below the n ≥ 5 non-solvability threshold not yet closed is `S₄`, which by the
reduction needs solvability of the alternating group `A₄` (order 12).

`A₄` is solvable because it has the Klein-four normal subgroup
`V₄ = {1, (12)(34), (13)(24), (14)(23)}` with abelian quotient `A₄ / V₄ ≅ ℤ/3`.
Equivalently, its derived series is `A₄ ⊳ V₄ ⊳ 1`.

This companion isolates that single fact for proof search.
-/

namespace AbelRuffiniOQ06Aristotle

open Equiv

/-- Reduction (proved in the verified file, restated here standalone): if the
alternating group is solvable then the full symmetric group is solvable. -/
theorem permSolvable_of_alternatingSolvable (n : ℕ)
    [IsSolvable (alternatingGroup (Fin n))] :
    IsSolvable (Equiv.Perm (Fin n)) :=
  solvable_of_ker_le_range (alternatingGroup (Fin n)).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact alternatingGroup_eq_sign_ker.ge)

/-- The alternating group `A₄` is solvable (derived series `A₄ ⊳ V₄ ⊳ 1`). -/
theorem alternatingFinFour_isSolvable : IsSolvable (alternatingGroup (Fin 4)) := by
  sorry

/-- `S₄ = Equiv.Perm (Fin 4)` is solvable. -/
theorem permFinFour_isSolvable : IsSolvable (Equiv.Perm (Fin 4)) := by
  haveI := alternatingFinFour_isSolvable
  exact permSolvable_of_alternatingSolvable 4

end AbelRuffiniOQ06Aristotle
