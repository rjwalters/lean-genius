import Proofs.Erdos85GeneralResidualOwnerTransportCells
import Proofs.Erdos85TwoPoleComplementaryOwnerExit

/-!
# Separation-free cross-witness two-pole owner terminal

The general residual owner ledger retains ambient-adjacent cut pairs through
the explicit triangle correction.  Consequently the two-pole owner terminal
needs no separation assumption: residual character one and the occurrence
pairing alone give the direct-through/complementary-exit alternative.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **General cross-witness two-pole terminal (`73rnz_cjibkzt`).**  Without
any ambient separation hypothesis, residual character one plus a free
two-pole involution yields either a direct cross-owner through or a uniquely
charged owner whose complement has a concrete ordinary exit carrying the
unique correction to `(1,1)`. -/
theorem generalCrossWitness_twoPole_crossOwner_or_complementaryOrdinaryExit
    {V O : Type*} [Fintype V] [DecidableEq V] [DecidableEq O]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V) (pairOwner : V × V → Bool)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1)
    (mate : O → O) (S : Finset O) (pole : Bool → O)
    (hpole : ∀ owner, pole owner ∈ S)
    (hpoles : Function.Injective pole)
    (hclosed : ∀ o ∈ S, mate o ∈ S)
    (hinvol : ∀ o ∈ S, mate (mate o) = o)
    (hfree : ∀ o ∈ S, mate o ≠ o) :
    let L := generalResidualOwnerTransportLedger A hq hreg
      (crossWitnessPairPopulation R) Prod.fst Prod.snd pairOwner
    mate (pole false) = pole true ∨
      ∃! charged : Bool,
        L.ownerSourceMass charged = 1 ∧
        twoPoleOwnerExit mate pole (!charged) ∈
          twoPoleOrdinaryOccurrences S (pole false) (pole true) ∧
        ∀ special : Bool → ZMod 2,
          (∀ j, L.ownerSourceMass j + special j = 1) ↔
            special = boolOwnerUnit (!charged) := by
  let L := generalResidualOwnerTransportLedger A hq hreg
    (crossWitnessPairPopulation R) Prod.fst Prod.snd pairOwner
  have hodd : (∑ i : Bool, L.ownerSourceMass i) = 1 :=
    sum_generalCrossWitnessOwnerSourceMass_eq_one
      A hq hreg R pairOwner hcharacter
  exact twoPole_crossOwner_or_existsUnique_complementaryOrdinaryExit
    L.ownerSourceMass hodd mate S pole hpole hpoles hclosed hinvol hfree

end


end Erdos85

#print axioms Erdos85.generalCrossWitness_twoPole_crossOwner_or_complementaryOrdinaryExit
