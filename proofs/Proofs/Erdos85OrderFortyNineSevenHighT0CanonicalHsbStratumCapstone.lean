import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeMixedCapstone
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbCapstone

/-! # H7 stratum capstone from `hsb` evidence

Stratum-level wrappers.  This module imports `...MixedCapstone`, hence the
thirteen positive-triple LRAT certificate modules.
-/

namespace Erdos85

/-- H7 capstone: UNSAT of `cube ∧ hsb<depth>` for the 28 structural cubes. -/
theorem orderFortyNineStratumExcluded_seven_of_structuralHsbUnsat
    (depth : Nat)
    (hstruct : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf
          depth edgeCount typeIndex).Unsat) :
    OrderFortyNineStratumExcluded 7 :=
  orderFortyNineStratumExcluded_seven_of_canonicalCompletion
    (sevenHighT0Canonical_noCompletion_of_structuralHsbUnsat depth hstruct)

/-- H7 capstone: checked `hsb` leaves and covers for the 28 structural
cubes. -/
theorem orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence
    (depth : Nat)
    (hstruct : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    OrderFortyNineStratumExcluded 7 :=
  orderFortyNineStratumExcluded_seven_of_canonicalCompletion
    (sevenHighT0Canonical_noCompletion_of_structuralHsbEvidence depth hstruct)

end Erdos85

#print axioms Erdos85.orderFortyNineStratumExcluded_seven_of_structuralHsbUnsat
#print axioms Erdos85.orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence
