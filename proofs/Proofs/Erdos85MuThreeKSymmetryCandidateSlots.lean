import Proofs.Erdos85MuThreeKSymmetryShapeExhaustive

/-! # A fixed 22-slot index for the mu-three K candidates -/

namespace Erdos85

/-- Position indices in each of the ten sector enumerations.  Empty sectors
have a `Fin 0` payload, so the total type contains exactly the 22 surviving
tables without requiring a global reduction of the search enumerators. -/
inductive Mu3KCandidateSlot where
  | c16AllTf (i : Fin 1)
  | c16AllTriangle (i : Fin 3)
  | c88AllTf (i : Fin 1)
  | c88AllTriangle (i : Fin 13)
  | c88FirstTf (i : Fin 1)
  | c88SecondTf (i : Fin 1)
  | c106AllTf (i : Fin 1)
  | c106AllTriangle (i : Fin 0)
  | c106TenTf (i : Fin 0)
  | c106SixTf (i : Fin 1)
  deriving DecidableEq, Fintype

theorem mu3KCandidateSlot_card : Fintype.card Mu3KCandidateSlot = 22 := by
  decide

noncomputable def mu3KCandidateSlotEquivFin : Mu3KCandidateSlot ≃ Fin 22 :=
  Fintype.equivFinOfCardEq mu3KCandidateSlot_card

def Mu3KCandidateSlot.sector : Mu3KCandidateSlot → Mu3KSectorChoice
  | .c16AllTf _ => .c16AllTf
  | .c16AllTriangle _ => .c16AllTriangle
  | .c88AllTf _ => .c88AllTf
  | .c88AllTriangle _ => .c88AllTriangle
  | .c88FirstTf _ => .c88FirstTf
  | .c88SecondTf _ => .c88SecondTf
  | .c106AllTf _ => .c106AllTf
  | .c106AllTriangle _ => .c106AllTriangle
  | .c106TenTf _ => .c106TenTf
  | .c106SixTf _ => .c106SixTf

def Mu3KCandidateSlot.position : Mu3KCandidateSlot → Nat
  | .c16AllTf i | .c16AllTriangle i
  | .c88AllTf i | .c88AllTriangle i
  | .c88FirstTf i | .c88SecondTf i
  | .c106AllTf i | .c106AllTriangle i
  | .c106TenTf i | .c106SixTf i => i.val

def Mu3KCandidateSlot.rows (slot : Mu3KCandidateSlot) : Mu3KRows :=
  (mu3KSectorEnumeration slot.sector.HRows slot.sector.TRows).getD
    slot.position []

end Erdos85

#print axioms Erdos85.mu3KCandidateSlot_card
#print axioms Erdos85.mu3KCandidateSlotEquivFin
