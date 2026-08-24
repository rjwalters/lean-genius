import Proofs.Erdos85CrossWitnessOwnerMass
import Proofs.Erdos85OwnerCutLedgerDiagonalCorrection

/-!
# The external owner cut is the literal ordinary-ledger source

Give every ordered residual-to-complement pair the owner of its residual
endpoint.  The source coordinate of the resulting graph-native ordinary
transport ledger is exactly the corresponding external owner cut mass.
Consequently each full owner cut is the actual ordinary-ledger source plus
the one shared internal cross-owner diagonal correction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The literal cross-witness ordinary ledger, with owner inherited from the
residual endpoint. -/
def crossWitnessOwnerTransportLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V) (owner : V → Bool)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z) :
    OwnerSourceTransportLedger (V × V) :=
  ordinaryResidualOwnerTransportLedger A hq hreg
    (crossWitnessPairPopulation R) Prod.fst Prod.snd
    (fun p => owner p.1)
    (crossWitnessPairPopulation_not_adj A R hseparated)

private theorem sum_product_filter_left
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (owner : X → Bool) (i : Bool)
    (f : X → Y → ZMod 2) :
    (∑ p ∈ (S ×ˢ T).filter (fun p => owner p.1 = i), f p.1 p.2) =
      ∑ x ∈ S.filter (fun x => owner x = i), ∑ y ∈ T, f x y := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases howner : owner x = i
  · simp [howner]
  · simp [howner]

/-- Each source coordinate of the literal graph-native ordinary ledger is
the matching external owner cut mass. -/
theorem ownerSourceMass_crossWitnessOwnerTransportLedger_eq_external
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V) (owner : V → Bool)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z)
    (i : Bool) :
    (crossWitnessOwnerTransportLedger A hq hreg R owner hseparated).ownerSourceMass i =
      ownerExternalCutMass (binaryTransportResidualGraph A hq hreg)
        R owner i := by
  unfold crossWitnessOwnerTransportLedger
    OwnerSourceTransportLedger.ownerSourceMass
    OwnerSourceTransportLedger.ownerCells
    ordinaryResidualOwnerTransportLedger
    ownerSourceTransportLedgerOfCells
    ownerExternalCutMass
    ownerWitnessCells
  simp only [Finset.sum_filter]
  unfold crossWitnessPairPopulation
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases howner : owner y = i
  · simp only [howner, if_true]
    apply Finset.sum_congr rfl
    intro z hz
    have hp : (y, z) ∈ R ×ˢ ordinaryWitnessComplement R :=
      Finset.mem_product.mpr ⟨hy, hz⟩
    simp [hp, ordinaryResidualOwnerTransportCell]
  · rw [if_neg howner]
    apply Finset.sum_eq_zero
    intro z hz
    have hp : (y, z) ∈ R ×ˢ ordinaryWitnessComplement R :=
      Finset.mem_product.mpr ⟨hy, hz⟩
    simp [hp, howner, ordinaryResidualOwnerTransportCell]

/-- **Owner-cut/ordinary-ledger bridge.**  The full physical cut of either
owner is its literal ordinary-ledger source coordinate plus the same internal
cross-owner diagonal correction. -/
theorem owner_cutMass_eq_crossWitnessLedgerSource_add_crossOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V) (owner : V → Bool)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z)
    (i : Bool) :
    (graphCutMass (binaryTransportResidualGraph A hq hreg)
      (ownerWitnessCells R owner i) : ZMod 2) =
      (crossWitnessOwnerTransportLedger A hq hreg R owner hseparated).ownerSourceMass i +
        residualCrossOwnerMass (binaryTransportResidualGraph A hq hreg)
          R owner := by
  rw [owner_cutMass_eq_external_add_crossOwner]
  rw [ownerSourceMass_crossWitnessOwnerTransportLedger_eq_external]

end

end Erdos85

#print axioms Erdos85.ownerSourceMass_crossWitnessOwnerTransportLedger_eq_external
#print axioms Erdos85.owner_cutMass_eq_crossWitnessLedgerSource_add_crossOwner
