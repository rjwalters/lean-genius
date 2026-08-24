import Proofs.Erdos85DiagonalOwnerDiscrepancy
import Proofs.Erdos85OwnerSourceTransportLedger

/-!
# Diagonal reduction of the concrete owner-demand ledger

The verified transport ledger identifies `Psi^hat_owner` with the two
owner-demand coordinates.  If only their scalar sum is known to vanish,
the diagonal discrepancy theorem reduces the entire vector to one scalar
coefficient.  The desired `(1,1)` conclusion is then exactly the assertion
that this coefficient is one.
-/

namespace Erdos85

namespace OwnerSourceTransportLedger

variable {C : Type*} [DecidableEq C]

/-- The owner-resolved demand before applying the local transport laws. -/
def ownerDemand (L : OwnerSourceTransportLedger C) (owner : Bool) : ZMod 2 :=
  L.ownerSourceMass owner + L.ownerRelayMass owner

/-- The corrected ledger vector is exactly its owner-demand vector. -/
theorem psiHatOwner_eq_ownerDemand (L : OwnerSourceTransportLedger C) :
    L.psiHatOwner = L.ownerDemand := by
  funext owner
  exact (L.ownerSourceMass_add_ownerRelayMass_eq_corrected owner).symm

/-- **Concrete diagonal reduction.**  Scalar demand conservation forces the
actual corrected ledger to be a diagonal owner vector.  Its single
coefficient is either owner coordinate. -/
theorem psiHatOwner_eq_diagonalOwnerVector_of_scalarDemand_zero
    (L : OwnerSourceTransportLedger C)
    (hscalar : L.ownerDemand false + L.ownerDemand true = 0) :
    L.psiHatOwner = diagonalOwnerVector (L.ownerDemand false) := by
  have heq : L.ownerDemand false = L.ownerDemand true :=
    f2_eq_of_add_eq_zero hscalar
  rw [psiHatOwner_eq_ownerDemand]
  funext owner
  cases owner
  · rfl
  · exact heq.symm

/-- Under scalar conservation, the full owner-resolved terminal is reduced
to one explicit coefficient.  This is the concrete ledger form of the
remaining `Delta` obstruction in `(73rnz_cjibkzd)`. -/
theorem psiHatOwner_eq_one_iff_false_ownerDemand_eq_one_of_scalarDemand_zero
    (L : OwnerSourceTransportLedger C)
    (hscalar : L.ownerDemand false + L.ownerDemand true = 0) :
    L.psiHatOwner = (fun _ : Bool => 1) ↔ L.ownerDemand false = 1 := by
  rw [psiHatOwner_eq_diagonalOwnerVector_of_scalarDemand_zero L hscalar]
  constructor
  · intro h
    exact congrFun h false
  · intro h
    funext owner
    exact h

end OwnerSourceTransportLedger

end Erdos85

#print axioms Erdos85.OwnerSourceTransportLedger.psiHatOwner_eq_ownerDemand
#print axioms Erdos85.OwnerSourceTransportLedger.psiHatOwner_eq_diagonalOwnerVector_of_scalarDemand_zero
#print axioms Erdos85.OwnerSourceTransportLedger.psiHatOwner_eq_one_iff_false_ownerDemand_eq_one_of_scalarDemand_zero
