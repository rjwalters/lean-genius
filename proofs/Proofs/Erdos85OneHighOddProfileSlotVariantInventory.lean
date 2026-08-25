import Proofs.Erdos85OneHighAllEvenCapacityInventory

/-! # Canonical slot variants of odd-profile all-even refinements

Pairing refinements sort their two edge keys by full pair code.  Canonical
leaf lex constraints only order the low endpoint of edge 01 before the low
endpoint of edge 23.  Thus two distinct keys with equal lows admit both edge
orders.  This executable inventory expands exactly that ambiguity while
keeping low/high orientation within each edge fixed.
-/

namespace Erdos85

/-- The canonical edge-slot orders compatible with one sorted source row. -/
def oneHighPairingRowSlotVariants
    (row : List OneHighLabelPair) : List (List OneHighLabelPair) :=
  match row with
  | [p, q] =>
      if p.1 = q.1 ∧ p ≠ q then [[p, q], [q, p]] else [[p, q]]
  | _ => [row]

/-- Independently choose a canonical edge order in every source row. -/
def oneHighRefinementSlotVariants
    (refinement : List (List OneHighLabelPair)) :
    List (List (List OneHighLabelPair)) :=
  oneHighChooseEach (refinement.map oneHighPairingRowSlotVariants)

/-- All exact all-even refinements attached to the capacity inventory of one
profile, before canonical edge-slot expansion. -/
def oneHighAllEvenCapacityInventoryRefinements (profile : Fin 5) :
    List (List (List OneHighLabelPair)) :=
  (oneHighAllEvenCapacityInventoryTables profile).flatMap fun table =>
    (oneHighPairingRefinements profile.val
      (oneHighPairingTableRestrict table)).filter
        oneHighRefinementAllOffDiagonalEven

/-- The complete profile-1/profile-3 canonical-slot target. -/
def oneHighOddProfileAllEvenSlotVariants :
    List (List (List OneHighLabelPair)) :=
  ([1, 3] : List (Fin 5)).flatMap fun profile =>
    (oneHighAllEvenCapacityInventoryRefinements profile).flatMap
      oneHighRefinementSlotVariants

theorem oneHighAllEvenCapacityInventoryRefinements_odd_lengths :
    (oneHighAllEvenCapacityInventoryRefinements 1).length = 64 ∧
      (oneHighAllEvenCapacityInventoryRefinements 3).length = 16 := by
  native_decide

/-- Forty of the eighty refinements have a genuine equal-low ambiguity; one
has two such rows.  Their exact canonical-slot expansion has 122 entries. -/
theorem oneHighOddProfileAllEvenSlotVariants_length :
    oneHighOddProfileAllEvenSlotVariants.length = 122 := by
  native_decide

end Erdos85

#print axioms Erdos85.oneHighAllEvenCapacityInventoryRefinements_odd_lengths
#print axioms Erdos85.oneHighOddProfileAllEvenSlotVariants_length
