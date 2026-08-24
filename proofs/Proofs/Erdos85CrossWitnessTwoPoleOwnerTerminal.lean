import Proofs.Erdos85CrossWitnessComplementSpecialDemand
import Proofs.Erdos85TwoPoleComplementaryOwnerExit

/-!
# Cross-witness character reaches the two-pole owner terminal

Combine the graph-native literal cut-pair ledger with the two-pole routing
alternative.  Residual character one leaves exactly two possibilities: the
two pole occurrences pair directly across owners, or the uniquely required
complementary owner has a concrete ordinary exit whose unit is the unique
correction to diagonal owner demand.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Cross-witness two-pole terminal.** -/
theorem crossWitness_twoPole_crossOwner_or_complementaryOrdinaryExit
    {V O : Type*} [Fintype V] [DecidableEq V] [DecidableEq O]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V) (witnessOwner : V → Bool)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1)
    (mate : O → O) (S : Finset O) (pole : Bool → O)
    (hpole : ∀ owner, pole owner ∈ S)
    (hpoles : Function.Injective pole)
    (hclosed : ∀ o ∈ S, mate o ∈ S)
    (hinvol : ∀ o ∈ S, mate (mate o) = o)
    (hfree : ∀ o ∈ S, mate o ≠ o) :
    let L := crossWitnessOwnerTransportLedger
      A hq hreg R witnessOwner hseparated
    mate (pole false) = pole true ∨
      ∃! charged : Bool,
        L.ownerSourceMass charged = 1 ∧
        twoPoleOwnerExit mate pole (!charged) ∈
          twoPoleOrdinaryOccurrences S (pole false) (pole true) ∧
        ∀ special : Bool → ZMod 2,
          (∀ j, L.ownerSourceMass j + special j = 1) ↔
            special = boolOwnerUnit (!charged) := by
  let L := crossWitnessOwnerTransportLedger
    A hq hreg R witnessOwner hseparated
  have hmass := sum_crossWitnessPairPopulation_residualIndicator_eq_one
    A hq hreg R hseparated hcharacter
  have hnotA := crossWitnessPairPopulation_not_adj A R hseparated
  have hodd : (∑ i : Bool, L.ownerSourceMass i) = 1 := by
    change (∑ i : Bool,
      (ordinaryResidualOwnerTransportLedger A hq hreg
        (crossWitnessPairPopulation R) Prod.fst Prod.snd
        (fun p : V × V => witnessOwner p.1) hnotA).ownerSourceMass i) = 1
    rw [sum_ownerSourceMass_ordinaryResidualOwnerTransportLedger]
    exact hmass
  exact twoPole_crossOwner_or_existsUnique_complementaryOrdinaryExit
    L.ownerSourceMass hodd mate S pole hpole hpoles hclosed hinvol hfree

end

end Erdos85

#print axioms Erdos85.crossWitness_twoPole_crossOwner_or_complementaryOrdinaryExit
