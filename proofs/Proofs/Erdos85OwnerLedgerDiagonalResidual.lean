import Proofs.Erdos85OwnerSourceTransportCells
import Proofs.Erdos85DiagonalOwnerDiscrepancy

/-!
# Diagonal residual in the concrete owner ledger

The centerwise commutator discrepancy is connected to the actual corrected
owner ledger.  Once its scalar sum vanishes center by center, the entire
unresolved contribution is one diagonal coefficient `Delta·(1,1)`.
-/

namespace Erdos85

open OwnerSourceTransportLedger

/-- A ledger decomposition into an audited base plus centerwise scalar-zero
owner discrepancies has exactly one diagonal residual coefficient. -/
theorem ownerLedger_eq_base_add_diagonalResidual
    {C G : Type*} [DecidableEq C] [DecidableEq G]
    (L : OwnerSourceTransportLedger C) (R : Finset G)
    (base : Bool → ZMod 2) (delta : Bool → G → ZMod 2)
    (hdecomp : ∀ owner,
      L.psiHatOwner owner = base owner + ∑ g ∈ R, delta owner g)
    (hzero : ∀ g ∈ R, delta false g + delta true g = 0) :
    L.psiHatOwner = fun owner =>
      base owner + diagonalOwnerVector
        (∑ g ∈ R, delta false g) owner := by
  have hdiag := sum_ownerDiscrepancy_eq_diagonalOwnerVector R delta hzero
  funext owner
  rw [hdecomp owner]
  exact congrArg (fun z => base owner + z) (congrFun hdiag owner)

/-- Under the same decomposition, recovering the audited base vector is
equivalent to killing the single diagonal residual coefficient. -/
theorem ownerLedger_eq_base_iff_diagonalResidual_eq_zero
    {C G : Type*} [DecidableEq C] [DecidableEq G]
    (L : OwnerSourceTransportLedger C) (R : Finset G)
    (base : Bool → ZMod 2) (delta : Bool → G → ZMod 2)
    (hdecomp : ∀ owner,
      L.psiHatOwner owner = base owner + ∑ g ∈ R, delta owner g)
    (hzero : ∀ g ∈ R, delta false g + delta true g = 0) :
    L.psiHatOwner = base ↔ (∑ g ∈ R, delta false g) = 0 := by
  let Delta : ZMod 2 := ∑ g ∈ R, delta false g
  have hshape := ownerLedger_eq_base_add_diagonalResidual
    L R base delta hdecomp hzero
  change L.psiHatOwner = base ↔ Delta = 0
  constructor
  · intro hbase
    have hf := congrFun hshape false
    rw [hbase] at hf
    change base false = base false + Delta at hf
    apply add_left_cancel (a := base false)
    simpa using hf.symm
  · intro hDelta
    have hDelta' : (∑ g ∈ R, delta false g) = 0 := hDelta
    rw [hshape]
    funext owner
    simp only [diagonalOwnerVector]
    rw [hDelta', add_zero]

/-- Specialization to the desired owner demand: after all audited base
terms give `(1,1)`, GAP `(73rnz_cjibkd)` is exactly `Delta=0`. -/
theorem psiHatOwner_eq_one_iff_diagonalResidual_eq_zero
    {C G : Type*} [DecidableEq C] [DecidableEq G]
    (L : OwnerSourceTransportLedger C) (R : Finset G)
    (delta : Bool → G → ZMod 2)
    (hdecomp : ∀ owner,
      L.psiHatOwner owner = 1 + ∑ g ∈ R, delta owner g)
    (hzero : ∀ g ∈ R, delta false g + delta true g = 0) :
    L.psiHatOwner = (fun _ : Bool => 1) ↔
      (∑ g ∈ R, delta false g) = 0 := by
  apply ownerLedger_eq_base_iff_diagonalResidual_eq_zero
    L R (fun _ => 1) delta
  · exact hdecomp
  · exact hzero

end Erdos85

#print axioms Erdos85.ownerLedger_eq_base_add_diagonalResidual
#print axioms Erdos85.ownerLedger_eq_base_iff_diagonalResidual_eq_zero
#print axioms Erdos85.psiHatOwner_eq_one_iff_diagonalResidual_eq_zero
