import Proofs.Erdos85GeneralResidualOwnerTransportCells
import Proofs.Erdos85OwnerExitSpecialContribution

/-!
# Owner-label provenance is a genuine missing interface

The full-cut pair owner and the special-leaf owner are currently independent
function arguments.  No theorem can derive that the leaf owner complements
the charged cut owner from those signatures alone: both functions may be
chosen constantly equal.  This file formalizes that interface countermodel.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- With a constant pair-owner labelling, all odd residual cut mass lies in
that prescribed owner coordinate. -/
theorem generalCrossWitness_constantOwner_sourceMass_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (R : Finset V) (charged : Bool)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    (generalResidualOwnerTransportLedger A hq hreg
      (crossWitnessPairPopulation R) Prod.fst Prod.snd
      (fun _ : V × V => charged)).ownerSourceMass charged = 1 := by
  unfold generalResidualOwnerTransportLedger
  unfold OwnerSourceTransportLedger.ownerSourceMass
    OwnerSourceTransportLedger.ownerCells
  simp only [ownerSourceTransportLedgerOfCells,
    generalResidualOwnerTransportCell]
  rw [Finset.filter_true]
  change (∑ p ∈ crossWitnessPairPopulation R,
    graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) p.1 p.2) = 1
  rw [show (∑ p ∈ crossWitnessPairPopulation R,
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) p.1 p.2) =
      ∑ y ∈ R, ∑ z ∈ ordinaryWitnessComplement R,
        graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) y z by
      unfold crossWitnessPairPopulation
      rw [Finset.sum_product]]
  rw [← graphCutMass_cast_eq_sum_indicator_complement]
  rw [← degreeParity_sum_eq_graphCutMass_cast]
  exact hcharacter

/-- The prescribed constant owner is the unique charged owner. -/
theorem generalCrossWitness_constantOwner_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (R : Finset V) (charged : Bool)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    let L := generalResidualOwnerTransportLedger A hq hreg
      (crossWitnessPairPopulation R) Prod.fst Prod.snd
      (fun _ : V × V => charged)
    L.ownerSourceMass charged = 1 ∧
      ∀ i, L.ownerSourceMass i = 1 → i = charged := by
  let L := generalResidualOwnerTransportLedger A hq hreg
    (crossWitnessPairPopulation R) Prod.fst Prod.snd
    (fun _ : V × V => charged)
  have hsum : (∑ i : Bool, L.ownerSourceMass i) = 1 :=
    sum_generalCrossWitnessOwnerSourceMass_eq_one
      A hq hreg R (fun _ : V × V => charged) hcharacter
  have hcharged : L.ownerSourceMass charged = 1 :=
    generalCrossWitness_constantOwner_sourceMass_eq_one
      A hq hreg R charged hcharacter
  obtain ⟨_witness, _hone, hunique⟩ :=
    existsUnique_owner_eq_one_of_sum_eq_one L.ownerSourceMass hsum
  exact ⟨hcharged, fun i hi => hunique i hi |>.trans (hunique charged hcharged).symm⟩

/-- **Owner-label provenance no-go (`73rnz_cjibkzu`).**  The current graph
and parity hypotheses admit owner assignments for which the unique charged
cut owner and the special leaf owner are equal, hence not complementary.
An actual coupling law between these labels is indispensable. -/
theorem exists_ownerLabels_specialLeaf_not_complementary
    {V O : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (R : Finset V) (l : O) (charged : Bool)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    ∃ pairOwner : V × V → Bool, ∃ leafOwner : O → Bool,
      let L := generalResidualOwnerTransportLedger A hq hreg
        (crossWitnessPairPopulation R) Prod.fst Prod.snd pairOwner
      L.ownerSourceMass charged = 1 ∧
        (∀ i, L.ownerSourceMass i = 1 → i = charged) ∧
        leafOwner l = charged ∧ leafOwner l ≠ !charged := by
  refine ⟨fun _ => charged, fun _ => charged, ?_⟩
  have hunique := generalCrossWitness_constantOwner_unique
    A hq hreg R charged hcharacter
  refine ⟨hunique.1, hunique.2, rfl, ?_⟩
  cases charged <;> simp

end


end Erdos85

#print axioms Erdos85.generalCrossWitness_constantOwner_sourceMass_eq_one
#print axioms Erdos85.exists_ownerLabels_specialLeaf_not_complementary
