import Mathlib
import Proofs.PascalsHexagonOQ03Incomplete01

/-!
# Pascal's Hexagon OQ-03 (companion): the census is Mathlib's derangement number D₆

The parent file `PascalsHexagonOQ03Incomplete01.lean` enumerates the fixed-point-free
permutations of `Fin 6` — the four cycle-type classes `6`, `(4,2)`, `(3,3)`, `(2,2,2)` of
sizes `120, 90, 40, 15` — and proves `card_fixedPointFree = 265` (by `native_decide`),
noting in prose that `265` is "the sixth derangement number `D₆`" and that
`FixedPointFree σ` is "membership in `derangements (Fin 6)`".

This companion makes those two remarks precise against Mathlib's derangement theory
(`Mathlib.Combinatorics.Derangements`):

* `numDerangements_six` — Mathlib's `Nat.numDerangements 6 = 265`, purely by kernel
  computation (the recurrence `numDerangements_add_two` is definitional).
* `fixedPointFree_iff_mem_derangements` — the parent's `FixedPointFree` predicate is
  *literally* membership in Mathlib's `derangements (Fin 6) = {σ | ∀ x, σ x ≠ x}`
  (definitional).
* `card_fixedPointFree_eq_numDerangements` — the parent's census count equals
  `Nat.numDerangements 6`, tying the geometric Hexagrammum census to the standard
  derangement number.

The first two are axiom-free; the third inherits `Lean.ofReduceBool` from the parent's
`native_decide`-proved `card_fixedPointFree`. 0 sorries.
-/

namespace PascalsHexagonOQ03Incomplete01

open Equiv Finset

/-- **`D₆ = 265`.** Mathlib's sixth derangement number, by kernel computation (the
recurrence `Nat.numDerangements_add_two` holds definitionally, so `decide` reduces the
whole chain `265 = 5·(9 + 44)`). -/
theorem numDerangements_six : Nat.numDerangements 6 = 265 := by decide

/-- **The census predicate is derangement-set membership.**  `FixedPointFree σ`
(`∀ i, σ i ≠ i`) is definitionally Mathlib's `σ ∈ derangements (Fin 6)`, since
`derangements (Fin 6) = {σ | ∀ x, σ x ≠ x}`. -/
theorem fixedPointFree_iff_mem_derangements (σ : Equiv.Perm (Fin 6)) :
    FixedPointFree σ ↔ σ ∈ derangements (Fin 6) := Iff.rfl

/-- **The Hexagrammum census equals the derangement number `D₆`.**  The parent's count
of fixed-point-free permutations of `Fin 6` is exactly `Nat.numDerangements 6`, making
rigorous the prose identification of `265` with `D₆`.  (Inherits `Lean.ofReduceBool`
from the parent's `native_decide` count `card_fixedPointFree`.) -/
theorem card_fixedPointFree_eq_numDerangements :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => FixedPointFree σ)).card
      = Nat.numDerangements 6 := by
  rw [card_fixedPointFree, numDerangements_six]

end PascalsHexagonOQ03Incomplete01
