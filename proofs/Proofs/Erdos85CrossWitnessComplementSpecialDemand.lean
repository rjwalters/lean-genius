import Proofs.Erdos85OwnerCutOrdinaryLedgerBridge
import Proofs.Erdos85OwnerComplementSpecialContribution
import Proofs.Erdos85OwnerDiagonalCorrectionNoGo

/-!
# Exact complementary special demand from a cross-witness character

For the literal residual-to-complement ordinary ledger, residual character
one determines a unique charged owner.  The unique vector which upgrades its
ordinary source to diagonal `(1,1)` demand is the unit in the complementary
owner.  The shared internal cross-owner cut correction cannot do this: being
diagonal, it preserves odd aggregate parity.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Cross-witness complementary special demand.**  On the literal
separated cut-pair ledger, character one uniquely determines both the charged
ordinary owner and the required complementary special correction. -/
theorem existsUnique_crossWitness_chargedOwner_and_specialCorrection
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V) (owner : V → Bool)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    let L := crossWitnessOwnerTransportLedger
      A hq hreg R owner hseparated
    ∃! charged : Bool,
      L.ownerSourceMass charged = 1 ∧
      (∀ special : Bool → ZMod 2,
        (∀ j, L.ownerSourceMass j + special j = 1) ↔
          special = boolOwnerUnit (!charged)) := by
  have hnotA := crossWitnessPairPopulation_not_adj A R hseparated
  have hodd := sum_crossWitnessPairPopulation_residualIndicator_eq_one
    A hq hreg R hseparated hcharacter
  simpa only [crossWitnessOwnerTransportLedger] using
    (existsUnique_chargedOwner_and_specialCorrection
      A hq hreg (crossWitnessPairPopulation R) Prod.fst Prod.snd
      (fun p : V × V => owner p.1) hnotA hodd)

/-- The shared internal cross-owner cut mass is not the required special
correction: adding it to both ordinary owner coordinates cannot produce
diagonal demand. -/
theorem crossWitness_crossOwnerMass_not_specialCorrection
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V) (owner : V → Bool)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    ¬ ∀ i : Bool,
      (crossWitnessOwnerTransportLedger A hq hreg R owner hseparated).ownerSourceMass i +
        residualCrossOwnerMass (binaryTransportResidualGraph A hq hreg)
          R owner = 1 := by
  have hnotA := crossWitnessPairPopulation_not_adj A R hseparated
  have hodd := sum_crossWitnessPairPopulation_residualIndicator_eq_one
    A hq hreg R hseparated hcharacter
  simpa only [crossWitnessOwnerTransportLedger] using
    (ordinaryResidualOwnerMass_not_diagonal_of_sharedCorrection
      A hq hreg (crossWitnessPairPopulation R) Prod.fst Prod.snd
      (fun p : V × V => owner p.1) hnotA hodd
      (residualCrossOwnerMass (binaryTransportResidualGraph A hq hreg)
        R owner))

end

end Erdos85

#print axioms Erdos85.existsUnique_crossWitness_chargedOwner_and_specialCorrection
#print axioms Erdos85.crossWitness_crossOwnerMass_not_specialCorrection
