import Proofs.Erdos85WitnessLabelCutCharacter
import Proofs.Erdos85OrdinaryResidualNuMuMass

/-!
# Cross-witness character transports into ordinary nu/mu mass

Take the witness graph to be the binary residual graph `K`.  If a residual
witness set `R` is separated from its complement in the ambient graph `A`,
then every `K`-cut incidence is an ordinary non-`A` pair and hence has the
graph-native decomposition `K = nu + mu`.  Character one across `R` therefore
becomes exactly one unit of corrected ordinary `nu+mu` mass.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The complement of `R` is the ordinary witness set used by the cut
ledger. -/
def ordinaryWitnessComplement {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) : Finset V := Finset.univ \ R

/-- Residual-graph neighbors in the ordinary complement are exactly the
graph-cut neighbors. -/
theorem neighbor_inter_ordinaryWitnessComplement
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (y : V) (R : Finset V) :
    K.neighborFinset y ∩ ordinaryWitnessComplement R =
      K.neighborFinset y \ R := by
  ext z
  simp [ordinaryWitnessComplement]

/-- **Cross-witness ordinary conservation (`73rnz_cjibkzl`).**  A residual
character of one in the binary residual graph is exactly one unit of the
double-summed ordinary `nu+mu` mass across the residual/nonresidual cut. -/
theorem sum_ordinaryResidualNuMuMass_crossWitness_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V)
    (hseparated : ∀ y ∈ R, ∀ z ∉ R, ¬ A.Adj y z)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    (∑ y ∈ R,
      ordinaryResidualNuMuMass A y (ordinaryWitnessComplement R)) = 1 := by
  let K := binaryTransportResidualGraph A hq hreg
  have hcut : (graphCutMass K R : ZMod 2) = 1 := by
    rw [← degreeParity_sum_eq_graphCutMass_cast K R]
    exact hcharacter
  have hcutSum :
      (∑ y ∈ R, (((K.neighborFinset y \ R).card : ℕ) : ZMod 2)) = 1 := by
    unfold graphCutMass at hcut
    push_cast at hcut
    exact hcut
  calc
    (∑ y ∈ R,
        ordinaryResidualNuMuMass A y (ordinaryWitnessComplement R)) =
        ∑ y ∈ R,
          ((((K.neighborFinset y ∩ ordinaryWitnessComplement R).card : ℕ) :
            ZMod 2)) := by
      apply Finset.sum_congr rfl
      intro y hy
      symm
      exact residual_neighbor_inter_card_cast_eq_ordinaryResidualNuMuMass
        A hq hreg y (ordinaryWitnessComplement R) (by
          intro z hz
          exact hseparated y hy z (by
            simpa [ordinaryWitnessComplement] using hz))
    _ = ∑ y ∈ R,
        (((K.neighborFinset y \ R).card : ℕ) : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [neighbor_inter_ordinaryWitnessComplement]
    _ = 1 := hcutSum

end


end Erdos85

#print axioms Erdos85.neighbor_inter_ordinaryWitnessComplement
#print axioms Erdos85.sum_ordinaryResidualNuMuMass_crossWitness_eq_one
