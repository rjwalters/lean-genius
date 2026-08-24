import Proofs.Erdos85CrossWitnessNuMuConservation
import Proofs.Erdos85OrdinaryResidualOwnerMassSplit

/-!
# Cross-witness character reaches a concrete owner fibre

The literal residual/nonresidual cut-pair population carries the graph-native
ordinary owner ledger.  In the ambient-`A` separated branch, residual
character one makes its total residual-`K` source odd, hence one actual owner
fibre is odd.  The conclusion intentionally does not claim that both owner
coordinates are one; that remains the separate owner-demand interface.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered residual-to-complement pairs forming the physical witness cut. -/
def crossWitnessPairPopulation
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) : Finset (V × V) :=
  R ×ˢ ordinaryWitnessComplement R

/-- Every literal cut pair is a non-`A` pair under ambient separation. -/
theorem crossWitnessPairPopulation_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) (R : Finset V)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z) :
    ∀ p ∈ crossWitnessPairPopulation R, ¬ A.Adj p.1 p.2 := by
  intro p hp
  have hparts := Finset.mem_product.mp hp
  exact hseparated p.1 hparts.1 p.2 (by
    simpa [ordinaryWitnessComplement] using hparts.2)

/-- Residual character one is exactly odd total residual-`K` source mass on
the literal separated cross-witness pair population. -/
theorem sum_crossWitnessPairPopulation_residualIndicator_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    (∑ p ∈ crossWitnessPairPopulation R,
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) p.1 p.2) = 1 := by
  have hmass := sum_ordinaryResidualNuMuMass_crossWitness_eq_one
    A hq hreg R hseparated hcharacter
  calc
    (∑ p ∈ crossWitnessPairPopulation R,
        graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) p.1 p.2) =
        ∑ y ∈ R, ∑ z ∈ ordinaryWitnessComplement R,
          graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) y z := by
      unfold crossWitnessPairPopulation
      rw [Finset.sum_product]
    _ = ∑ y ∈ R,
        ordinaryResidualNuMuMass A y (ordinaryWitnessComplement R) := by
      apply Finset.sum_congr rfl
      intro y hy
      unfold ordinaryResidualNuMuMass
      apply Finset.sum_congr rfl
      intro z hz
      rw [graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_of_not_adj
        A hq hreg (hseparated y hy z (by
          simpa [ordinaryWitnessComplement] using hz))]
    _ = 1 := hmass

/-- **Cross-witness owner extraction.**  Label every literal cut pair by
either pole owner.  A separated residual character of one forces a concrete
owner fibre of the resulting graph-native ordinary ledger to carry one unit
of residual source mass. -/
theorem exists_ownerSourceMass_eq_one_of_crossWitness_character
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V) (owner : V × V → Bool)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    ∃ i : Bool,
      (ordinaryResidualOwnerTransportLedger A hq hreg
        (crossWitnessPairPopulation R) Prod.fst Prod.snd owner
        (crossWitnessPairPopulation_not_adj A R hseparated)).ownerSourceMass i = 1 := by
  apply exists_ownerSourceMass_eq_one_of_ordinaryResidual_K_mass_eq_one
    A hq hreg (crossWitnessPairPopulation R) Prod.fst Prod.snd owner
      (crossWitnessPairPopulation_not_adj A R hseparated)
  exact sum_crossWitnessPairPopulation_residualIndicator_eq_one
    A hq hreg R hseparated hcharacter

end

end Erdos85

#print axioms Erdos85.crossWitnessPairPopulation_not_adj
#print axioms Erdos85.sum_crossWitnessPairPopulation_residualIndicator_eq_one
#print axioms Erdos85.exists_ownerSourceMass_eq_one_of_crossWitness_character
