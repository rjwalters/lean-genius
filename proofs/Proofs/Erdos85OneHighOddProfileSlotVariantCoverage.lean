import Proofs.Erdos85OneHighOddProfileSlotVariantInventory

/-! # Membership interface for odd-profile canonical-slot variants

This file separates the small structural coverage argument from the executable
122-row census.  A slot assignment is covered precisely when each of its rows
chooses one of the edge orders admitted by the corresponding sorted pairing
row.  The global inventory then follows by two ordinary `flatMap` membership
steps.
-/

namespace Erdos85

/-- Pointwise specification of a canonical-slot expansion of one sorted
pairing refinement. -/
def OneHighRefinementSlotCompatible
    (sorted slots : List (List OneHighLabelPair)) : Prop :=
  OneHighChoicesCompatible
    (sorted.map oneHighPairingRowSlotVariants) slots

theorem oneHighRefinementSlotVariants_mem_iff
    (sorted slots : List (List OneHighLabelPair)) :
    slots ∈ oneHighRefinementSlotVariants sorted ↔
      OneHighRefinementSlotCompatible sorted slots := by
  exact oneHighChooseEach_mem_iff _ _

/-- A pointwise-compatible slot assignment is present in the exact expansion
of its authoritative sorted refinement. -/
theorem oneHighRefinementSlotVariants_mem
    {sorted slots : List (List OneHighLabelPair)}
    (hslots : OneHighRefinementSlotCompatible sorted slots) :
    slots ∈ oneHighRefinementSlotVariants sorted :=
  (oneHighRefinementSlotVariants_mem_iff sorted slots).2 hslots

/-- Lift one compatible slot assignment through a fixed odd profile's
all-even capacity inventory. -/
theorem oneHigh_slotVariant_mem_profile
    {profile : Fin 5}
    {sorted slots : List (List OneHighLabelPair)}
    (hsorted : sorted ∈
      oneHighAllEvenCapacityInventoryRefinements profile)
    (hslots : OneHighRefinementSlotCompatible sorted slots) :
    slots ∈ (oneHighAllEvenCapacityInventoryRefinements profile).flatMap
      oneHighRefinementSlotVariants := by
  exact List.mem_flatMap.mpr
    ⟨sorted, hsorted, oneHighRefinementSlotVariants_mem hslots⟩

/-- Profile one slot assignments enter the combined 122-instance target. -/
theorem oneHigh_profileOne_slotVariant_mem
    {sorted slots : List (List OneHighLabelPair)}
    (hsorted : sorted ∈
      oneHighAllEvenCapacityInventoryRefinements (1 : Fin 5))
    (hslots : OneHighRefinementSlotCompatible sorted slots) :
    slots ∈ oneHighOddProfileAllEvenSlotVariants := by
  rw [oneHighOddProfileAllEvenSlotVariants]
  apply List.mem_flatMap.mpr
  refine ⟨(1 : Fin 5), by simp, ?_⟩
  exact oneHigh_slotVariant_mem_profile hsorted hslots

/-- Profile three slot assignments enter the combined 122-instance target. -/
theorem oneHigh_profileThree_slotVariant_mem
    {sorted slots : List (List OneHighLabelPair)}
    (hsorted : sorted ∈
      oneHighAllEvenCapacityInventoryRefinements (3 : Fin 5))
    (hslots : OneHighRefinementSlotCompatible sorted slots) :
    slots ∈ oneHighOddProfileAllEvenSlotVariants := by
  rw [oneHighOddProfileAllEvenSlotVariants]
  apply List.mem_flatMap.mpr
  refine ⟨(3 : Fin 5), by simp, ?_⟩
  exact oneHigh_slotVariant_mem_profile hsorted hslots

end Erdos85

#print axioms Erdos85.oneHigh_profileOne_slotVariant_mem
#print axioms Erdos85.oneHigh_profileThree_slotVariant_mem
