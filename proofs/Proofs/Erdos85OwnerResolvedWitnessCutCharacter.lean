import Proofs.Erdos85WitnessLabelCutCharacter

/-!
# Owner-resolved witness cut character

Scalar residual cut parity forgets which pole owner carries the charge.  A
Boolean owner map gives a genuine nonconstant refinement: intersect the
residual set with each owner fibre and apply the handshake identity there.
The two owner cut characters recombine to the original residual character,
so an odd residual cut selects an owner with an odd physical cut edge.
-/

open SimpleGraph

namespace Erdos85

/-- Residual witnesses belonging to one Boolean owner. -/
def ownerWitnessCells
    {V : Type*} [DecidableEq V]
    (R : Finset V) (owner : V → Bool) (i : Bool) : Finset V :=
  R.filter fun y => owner y = i

/-- Each owner-resolved degree character is exactly the physical cut mass of
that owner cell. -/
theorem owner_degreeCharacter_eq_cutMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj]
    (R : Finset V) (owner : V → Bool) (i : Bool) :
    (∑ y ∈ ownerWitnessCells R owner i, (W.degree y : ZMod 2)) =
      (graphCutMass W (ownerWitnessCells R owner i) : ZMod 2) :=
  degreeParity_sum_eq_graphCutMass_cast W (ownerWitnessCells R owner i)

/-- The two owner-resolved characters recombine exactly to the scalar
residual character.  Cross-owner internal edges occur in both owner cuts and
therefore cancel over `F₂`. -/
theorem owner_cutMass_false_add_true_eq_residualCutMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj]
    (R : Finset V) (owner : V → Bool) :
    (graphCutMass W (ownerWitnessCells R owner false) : ZMod 2) +
      (graphCutMass W (ownerWitnessCells R owner true) : ZMod 2) =
      (graphCutMass W R : ZMod 2) := by
  rw [← owner_degreeCharacter_eq_cutMass W R owner false,
    ← owner_degreeCharacter_eq_cutMass W R owner true,
    ← degreeParity_sum_eq_graphCutMass_cast W R]
  simp only [ownerWitnessCells, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  cases owner y <;> simp

/-- Character one selects a concrete owner cell whose physical cut is odd. -/
theorem exists_owner_cutMass_eq_one_of_residualCharacter_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj]
    (R : Finset V) (owner : V → Bool)
    (hcharacter : (∑ y ∈ R, (W.degree y : ZMod 2)) = 1) :
    ∃ i : Bool,
      (graphCutMass W (ownerWitnessCells R owner i) : ZMod 2) = 1 := by
  have hresidualCut : (graphCutMass W R : ZMod 2) = 1 := by
    rw [← degreeParity_sum_eq_graphCutMass_cast W R]
    exact hcharacter
  have hsum :
      (graphCutMass W (ownerWitnessCells R owner false) : ZMod 2) +
        (graphCutMass W (ownerWitnessCells R owner true) : ZMod 2) = 1 := by
    rw [owner_cutMass_false_add_true_eq_residualCutMass W R owner,
      hresidualCut]
  have hcases :
      (graphCutMass W (ownerWitnessCells R owner false) : ZMod 2) = 0 ∨
        (graphCutMass W (ownerWitnessCells R owner false) : ZMod 2) = 1 := by
    generalize (graphCutMass W (ownerWitnessCells R owner false) : ZMod 2) = x
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases with hzero | hone
  · refine ⟨true, ?_⟩
    rw [hzero, zero_add] at hsum
    exact hsum
  · exact ⟨false, hone⟩

/-- **Owner-resolved physical exit (`73rnz_cjibkzn-owner`).**  An odd
residual character forces an owner with odd cut mass and a concrete edge
leaving that owner cell. -/
theorem exists_owner_crossWitness_edge_of_residualCharacter_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj]
    (R : Finset V) (owner : V → Bool)
    (hcharacter : (∑ y ∈ R, (W.degree y : ZMod 2)) = 1) :
    ∃ i : Bool,
      (graphCutMass W (ownerWitnessCells R owner i) : ZMod 2) = 1 ∧
      ∃ y ∈ ownerWitnessCells R owner i,
        ∃ z ∉ ownerWitnessCells R owner i, W.Adj y z := by
  obtain ⟨i, hcut⟩ :=
    exists_owner_cutMass_eq_one_of_residualCharacter_one W R owner hcharacter
  have hdegree :
      (∑ y ∈ ownerWitnessCells R owner i, (W.degree y : ZMod 2)) = 1 := by
    rw [owner_degreeCharacter_eq_cutMass, hcut]
  exact ⟨i, hcut,
    exists_crossWitness_edge_of_degreeParity_sum_eq_one
      W (ownerWitnessCells R owner i) hdegree⟩

end Erdos85

#print axioms Erdos85.owner_degreeCharacter_eq_cutMass
#print axioms Erdos85.owner_cutMass_false_add_true_eq_residualCutMass
#print axioms Erdos85.exists_owner_crossWitness_edge_of_residualCharacter_one
