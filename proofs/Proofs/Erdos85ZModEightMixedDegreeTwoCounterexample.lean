import Proofs.Erdos85ZModEightSameParitySingleIntertwiner

/-!
# A mixed-parity degree-two C8 self-intertwiner

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

This file records a counterexample to a tempting parameter-five shortcut.
Symmetry, looplessness, row degree two, and the C8 self-intertwining
recurrence do **not** force the two neighbours in a row to have the same
parity.  The matrix below is the union of the half-turn matching
`y = x + 4` and the reflection matching `y = 7 - x`.

Consequently the parameter-five `8+8` branch needs an additional graph-level
constraint; the bare commuting-matrix argument cannot exclude its mixed
one-same/one-opposite diagonal block.
-/

namespace Erdos85

/-- Half-turn plus an odd reflection matching on `ZMod 8`. -/
def zmodEightMixedDegreeTwoIntertwiner : Matrix (ZMod 8) (ZMod 8) ℤ :=
  fun x y => if y = x + 4 ∨ y = 7 - x then 1 else 0

/-- The explicit mixed matrix is loopless, symmetric, binary, two-regular,
and satisfies the C8 self-intertwining recurrence. -/
theorem zmodEightMixedDegreeTwoIntertwiner_spec :
    (∀ x, zmodEightMixedDegreeTwoIntertwiner x x = 0) ∧
    (∀ x y, zmodEightMixedDegreeTwoIntertwiner x y =
      zmodEightMixedDegreeTwoIntertwiner y x) ∧
    (∀ x y, zmodEightMixedDegreeTwoIntertwiner x y = 0 ∨
      zmodEightMixedDegreeTwoIntertwiner x y = 1) ∧
    (∀ x, ∑ y, zmodEightMixedDegreeTwoIntertwiner x y = 2) ∧
    (∀ x y,
      zmodEightMixedDegreeTwoIntertwiner (x - 1) y +
          zmodEightMixedDegreeTwoIntertwiner (x + 1) y =
        zmodEightMixedDegreeTwoIntertwiner x (y + 1) +
          zmodEightMixedDegreeTwoIntertwiner x (y - 1)) := by
  decide

/-- Every row of the explicit self-intertwiner has exactly one same-parity
and exactly one opposite-parity entry. -/
theorem zmodEightMixedDegreeTwoIntertwiner_parity_split :
    (∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ZModEightEvenOffset (y - x) ∧
          zmodEightMixedDegreeTwoIntertwiner x y = 1).card = 1) ∧
    (∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ¬ ZModEightEvenOffset (y - x) ∧
          zmodEightMixedDegreeTwoIntertwiner x y = 1).card = 1) := by
  decide

end Erdos85

#print axioms Erdos85.zmodEightMixedDegreeTwoIntertwiner_spec
#print axioms Erdos85.zmodEightMixedDegreeTwoIntertwiner_parity_split
