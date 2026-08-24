import Proofs.Erdos85OwnerSourceTransportLedger

/-!
# Verified private owner-transport cells

The four local Baer owner normal forms are packaged as verified cells and
can be assembled mechanically into the concrete `Psi^hat_owner` ledger.
-/

namespace Erdos85

/-- One private owner-labeled occurrence cell with its verified corrected
source-transport value. -/
structure OwnerSourceTransportCell where
  owner : Bool
  source : ZMod 2
  relay : ZMod 2
  corrected : ZMod 2
  transport : source + relay = corrected

/-- A finite population of verified private cells automatically forms an
owner source-transport ledger. -/
def ownerSourceTransportLedgerOfCells
    {C : Type*} [DecidableEq C] (S : Finset C)
    (cell : C → OwnerSourceTransportCell) : OwnerSourceTransportLedger C where
  cells := S
  owner c := (cell c).owner
  source c := (cell c).source
  relay c := (cell c).relay
  corrected c := (cell c).corrected
  transport c _ := (cell c).transport

/-- Verified active-switch cell from `(73rnz_cjibk)`. -/
def activeSwitchTransportCell
    (owner : Bool) (kSource kRelay rho mu : ZMod 2)
    (hsource : kSource = 1 + rho)
    (hrelay : kRelay = 1 + mu) : OwnerSourceTransportCell where
  owner := owner
  source := kSource
  relay := kRelay
  corrected := rho + mu
  transport := activeSwitch_sourceTransport
    kSource kRelay rho mu hsource hrelay

/-- Verified collision cell from `(73rnz_cjibka)`, retaining the inactive
port parity in its corrected value. -/
def collisionTransportCell
    {I : Type*} [DecidableEq I] (owner : Bool)
    (activePorts : Finset I)
    (kSource rho c cActive cInactive : ZMod 2)
    (kRelay mu : I → ZMod 2)
    (hcount : c = cActive + cInactive)
    (hsource : kSource = c + rho)
    (hrelay : (∑ i ∈ activePorts, kRelay i) =
      cActive + ∑ i ∈ activePorts, mu i) : OwnerSourceTransportCell where
  owner := owner
  source := kSource
  relay := ∑ i ∈ activePorts, kRelay i
  corrected := cInactive + rho + ∑ i ∈ activePorts, mu i
  transport := collision_sourceTransport activePorts
    kSource rho c cActive cInactive kRelay mu hcount hsource hrelay

/-- Verified active direct-exit cell from `(73rnz_cjibkb)`. -/
def activeDirectExitTransportCell
    (owner : Bool) (kSource kRelay muSource muRelay : ZMod 2)
    (hsource : kSource = 1 + muSource)
    (hrelay : kRelay = 1 + muRelay) : OwnerSourceTransportCell where
  owner := owner
  source := kSource
  relay := kRelay
  corrected := muSource + muRelay
  transport := activeDirectExit_sourceTransport
    kSource kRelay muSource muRelay hsource hrelay

/-- Verified active cross-star-through cell from `(73rnz_cjibkc)`.  A
through contributes once to each owner by inserting the corresponding
verified cell twice with the two Bool labels. -/
def activeCrossStarThroughTransportCell
    (owner : Bool) (sourceCell kRelay muRelay : ZMod 2)
    (hsource : sourceCell = 1)
    (hrelay : kRelay = 1 + muRelay) : OwnerSourceTransportCell where
  owner := owner
  source := sourceCell
  relay := kRelay
  corrected := muRelay
  transport := activeCrossStarThrough_sourceTransport
    sourceCell kRelay muRelay hsource hrelay

/-- The corrected owner coordinate of a ledger assembled from cells is
definitionally the sum of their verified corrected values in that owner
fiber. -/
theorem psiHatOwner_ledgerOfCells_apply
    {C : Type*} [DecidableEq C] (S : Finset C)
    (cell : C → OwnerSourceTransportCell) (owner : Bool) :
    (ownerSourceTransportLedgerOfCells S cell).psiHatOwner owner =
      ∑ c ∈ S.filter (fun c => (cell c).owner = owner),
        (cell c).corrected := by
  rfl

end Erdos85

#print axioms Erdos85.activeSwitchTransportCell
#print axioms Erdos85.collisionTransportCell
#print axioms Erdos85.activeDirectExitTransportCell
#print axioms Erdos85.activeCrossStarThroughTransportCell
#print axioms Erdos85.psiHatOwner_ledgerOfCells_apply
