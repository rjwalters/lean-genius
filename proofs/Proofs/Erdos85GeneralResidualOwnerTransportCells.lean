import Proofs.Erdos85CrossWitnessOwnerMass
import Proofs.Erdos85CrossWitnessNuMuTriangleCorrection
import Proofs.Erdos85OwnerComplementSpecialContribution

/-!
# Owner transport cells on arbitrary residual pairs

The ordinary owner ledger required ambient-`A` separation because it used
`K = nu + mu`.  On an arbitrary pair the exact identity is
`K = nu + mu + T`.  Taking `nu` as relay and `mu+T` as corrected value gives
a verified owner cell without any separation hypothesis.  Applied to the
literal witness cut, residual character one again yields a unique charged
owner and its complementary special correction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Graph-native owner cell on an arbitrary pair, retaining the explicit
triangle-edge correction in its corrected value. -/
def generalResidualOwnerTransportCell
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (owner : Bool) (u v : V) : OwnerSourceTransportCell where
  owner := owner
  source := graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v
  relay := ordinaryNu A u v
  corrected := ordinaryMu A u v +
    graphEdgeIndicator (triangleFreeEdgeGraph A) u v
  transport := by
    rw [graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_add_triangle]
    change (ordinaryNu A u v + ordinaryMu A u v +
      graphEdgeIndicator (triangleFreeEdgeGraph A) u v) +
      ordinaryNu A u v = ordinaryMu A u v +
        graphEdgeIndicator (triangleFreeEdgeGraph A) u v
    have hnu : ordinaryNu A u v + ordinaryNu A u v = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
    calc
      (ordinaryNu A u v + ordinaryMu A u v +
          graphEdgeIndicator (triangleFreeEdgeGraph A) u v) +
          ordinaryNu A u v =
        (ordinaryNu A u v + ordinaryNu A u v) +
          (ordinaryMu A u v +
            graphEdgeIndicator (triangleFreeEdgeGraph A) u v) := by abel
      _ = ordinaryMu A u v +
          graphEdgeIndicator (triangleFreeEdgeGraph A) u v := by
        rw [hnu, zero_add]

/-- Assemble arbitrary labelled pairs into the separation-free owner ledger. -/
def generalResidualOwnerTransportLedger
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool) :
    OwnerSourceTransportLedger C :=
  ownerSourceTransportLedgerOfCells pairs fun c =>
    generalResidualOwnerTransportCell A hq hreg (owner c) (left c) (right c)

private theorem sum_bool_ownerSourceMass_eq_total
    {C : Type*} [DecidableEq C] (L : OwnerSourceTransportLedger C) :
    (∑ i : Bool, L.ownerSourceMass i) =
      ∑ c ∈ L.cells, L.source c := by
  classical
  unfold OwnerSourceTransportLedger.ownerSourceMass
    OwnerSourceTransportLedger.ownerCells
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_eq_single (L.owner c)]
  · simp
  · intro i _ hine
    simp [hine.symm]
  · simp

/-- Forgetting owner labels in the general ledger recovers literal residual
`K` source mass. -/
theorem sum_ownerSourceMass_generalResidualOwnerTransportLedger
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool) :
    (∑ i : Bool,
      (generalResidualOwnerTransportLedger A hq hreg
        pairs left right owner).ownerSourceMass i) =
      ∑ c ∈ pairs,
        graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
          (left c) (right c) := by
  rw [sum_bool_ownerSourceMass_eq_total]
  rfl

/-- Residual character one gives odd total source on the literal full cut,
with no ambient separation assumption. -/
theorem sum_generalCrossWitnessOwnerSourceMass_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (R : Finset V) (owner : V × V → Bool)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    (∑ i : Bool,
      OwnerSourceTransportLedger.ownerSourceMass
        (generalResidualOwnerTransportLedger A hq hreg
          (crossWitnessPairPopulation R) Prod.fst Prod.snd owner) i) = 1 := by
  rw [sum_ownerSourceMass_generalResidualOwnerTransportLedger]
  rw [show (∑ p ∈ crossWitnessPairPopulation R,
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) p.1 p.2) =
      ∑ y ∈ R, ∑ z ∈ ordinaryWitnessComplement R,
        graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) y z by
      unfold crossWitnessPairPopulation
      rw [Finset.sum_product]]
  rw [← graphCutMass_cast_eq_sum_indicator_complement]
  rw [← degreeParity_sum_eq_graphCutMass_cast]
  exact hcharacter

/-- **Separation-free owner terminal (`73rnz_cjibkzs`).**  On the literal
full witness cut, residual character one determines a unique charged owner;
the unique correction to diagonal demand is its complementary owner unit. -/
theorem existsUnique_generalCrossWitness_chargedOwner_and_specialCorrection
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (R : Finset V) (owner : V × V → Bool)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    let L := generalResidualOwnerTransportLedger A hq hreg
      (crossWitnessPairPopulation R) Prod.fst Prod.snd owner
    ∃! charged : Bool,
      L.ownerSourceMass charged = 1 ∧
      ∀ special : Bool → ZMod 2,
        (∀ j, L.ownerSourceMass j + special j = 1) ↔
          special = boolOwnerUnit (!charged) := by
  let L := generalResidualOwnerTransportLedger A hq hreg
    (crossWitnessPairPopulation R) Prod.fst Prod.snd owner
  have hsum : (∑ i : Bool, L.ownerSourceMass i) = 1 :=
    sum_generalCrossWitnessOwnerSourceMass_eq_one
      A hq hreg R owner hcharacter
  obtain ⟨charged, hcharged, hunique⟩ :=
    existsUnique_owner_eq_one_of_sum_eq_one L.ownerSourceMass hsum
  have hvector : L.ownerSourceMass = boolOwnerUnit charged :=
    eq_boolOwnerUnit_of_sum_eq_one_of_apply_eq_one
      L.ownerSourceMass hsum charged hcharged
  refine ⟨charged, ⟨hcharged, ?_⟩, ?_⟩
  · intro special
    rw [hvector]
    exact add_eq_one_iff_eq_complementOwnerUnit charged special
  · intro i hi
    exact hunique i hi.1

end


end Erdos85

#print axioms Erdos85.generalResidualOwnerTransportCell
#print axioms Erdos85.sum_generalCrossWitnessOwnerSourceMass_eq_one
#print axioms Erdos85.existsUnique_generalCrossWitness_chargedOwner_and_specialCorrection
