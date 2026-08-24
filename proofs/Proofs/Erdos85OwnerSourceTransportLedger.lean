import Proofs.Erdos85OwnerSourceTransportAlgebra

/-!
# Owner-indexed source-transport ledger

This is the first concrete Lean representation of the corrected owner vector
`Psi^hat_owner` from `(73rnz_cjibkd)`.  Every private cell retains its Bool
owner, source contribution, relay price, and corrected `rho`/`mu` value.
Local transport laws aggregate ownerwise without losing the diagonal class.
-/

namespace Erdos85

/-- A finite private occurrence ledger with a verified local source-
transport equation on every realized cell.  Inactive residues belong in
`corrected`; they are intentionally not erased from the structure. -/
structure OwnerSourceTransportLedger (C : Type*) [DecidableEq C] where
  cells : Finset C
  owner : C → Bool
  source : C → ZMod 2
  relay : C → ZMod 2
  corrected : C → ZMod 2
  transport : ∀ c ∈ cells, source c + relay c = corrected c

namespace OwnerSourceTransportLedger

variable {C : Type*} [DecidableEq C]

/-- Cells retained by one pole-owner character. -/
def ownerCells (L : OwnerSourceTransportLedger C) (i : Bool) : Finset C :=
  L.cells.filter fun c => L.owner c = i

/-- Owner-resolved source mass before transport. -/
def ownerSourceMass (L : OwnerSourceTransportLedger C) (i : Bool) : ZMod 2 :=
  ∑ c ∈ L.ownerCells i, L.source c

/-- Owner-resolved realized relay price. -/
def ownerRelayMass (L : OwnerSourceTransportLedger C) (i : Bool) : ZMod 2 :=
  ∑ c ∈ L.ownerCells i, L.relay c

/-- Corrected owner coordinate, including all active `rho`/`mu` terms and
uncancelled inactive source residues. -/
def ownerCorrectedMass
    (L : OwnerSourceTransportLedger C) (i : Bool) : ZMod 2 :=
  ∑ c ∈ L.ownerCells i, L.corrected c

/-- The actual corrected two-owner vector `Psi^hat_owner`. -/
def psiHatOwner (L : OwnerSourceTransportLedger C) : Bool → ZMod 2 :=
  fun i => L.ownerCorrectedMass i

/-- Local source transport aggregates independently in each owner
coordinate. -/
theorem ownerSourceMass_add_ownerRelayMass_eq_corrected
    (L : OwnerSourceTransportLedger C) (i : Bool) :
    L.ownerSourceMass i + L.ownerRelayMass i = L.ownerCorrectedMass i := by
  rw [ownerSourceMass, ownerRelayMass, ownerCorrectedMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  exact L.transport c (Finset.mem_filter.mp hc).1

/-- Exact conditional form of `(73rnz_cjibkd)`: once the remaining
owner-demand conservation theorem proves one unit in each coordinate, the
corrected transport vector is literally `(1,1)`. -/
theorem psiHatOwner_eq_one_of_ownerDemand
    (L : OwnerSourceTransportLedger C)
    (hdemand : ∀ i,
      L.ownerSourceMass i + L.ownerRelayMass i = 1) :
    L.psiHatOwner = fun _ : Bool => 1 := by
  funext i
  rw [psiHatOwner, ← ownerSourceMass_add_ownerRelayMass_eq_corrected]
  exact hdemand i

/-- Conversely, the corrected diagonal conclusion is equivalent to the
owner-demand equations; no scalar sum can replace either coordinate. -/
theorem psiHatOwner_eq_one_iff_ownerDemand
    (L : OwnerSourceTransportLedger C) :
    L.psiHatOwner = (fun _ : Bool => 1) ↔
      ∀ i, L.ownerSourceMass i + L.ownerRelayMass i = 1 := by
  constructor
  · intro h i
    rw [ownerSourceMass_add_ownerRelayMass_eq_corrected,
      ← psiHatOwner, h]
  · exact psiHatOwner_eq_one_of_ownerDemand L

end OwnerSourceTransportLedger

end Erdos85

#print axioms Erdos85.OwnerSourceTransportLedger.ownerSourceMass_add_ownerRelayMass_eq_corrected
#print axioms Erdos85.OwnerSourceTransportLedger.psiHatOwner_eq_one_of_ownerDemand
#print axioms Erdos85.OwnerSourceTransportLedger.psiHatOwner_eq_one_iff_ownerDemand
