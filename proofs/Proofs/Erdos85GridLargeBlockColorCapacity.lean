import Mathlib

/-!
# Large-block color capacities from two fiber strips

This is the inclusion-exclusion step producing the `7,4,4` capacities in
the `[2,2,2,2]`, `C10 + C6` fiber-margin obstruction.
-/

namespace Erdos85

/-- A color class of size sixteen meets each of the two small-coordinate
strips in six cells.  If their intersection has size three for one color and
zero for the others, the complementary large block has size `7` or `4`. -/
theorem largeBlockColor_card_eq_of_two_strips
    {V : Type*} [DecidableEq V]
    (fiber rowStrip columnStrip : Finset V) (isLarge : Prop)
    [Decidable isLarge]
    (hfiber : fiber.card = 16)
    (hrow : rowStrip.card = 6)
    (hcolumn : columnStrip.card = 6)
    (hrowSub : rowStrip ⊆ fiber)
    (hcolumnSub : columnStrip ⊆ fiber)
    (hinter : (rowStrip ∩ columnStrip).card = if isLarge then 3 else 0) :
    (fiber \ (rowStrip ∪ columnStrip)).card = if isLarge then 7 else 4 := by
  have hunionSub : rowStrip ∪ columnStrip ⊆ fiber :=
    Finset.union_subset hrowSub hcolumnSub
  have hunion : (rowStrip ∪ columnStrip).card =
      if isLarge then 9 else 12 := by
    rw [Finset.card_union, hrow, hcolumn, hinter]
    split <;> omega
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr hunionSub, hfiber, hunion]
  split <;> omega

end Erdos85

#print axioms Erdos85.largeBlockColor_card_eq_of_two_strips
