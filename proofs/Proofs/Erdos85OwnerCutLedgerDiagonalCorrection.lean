import Proofs.Erdos85OwnerResolvedWitnessCutCharacter
import Proofs.Erdos85CrossWitnessNuMuTriangleCorrection

/-!
# Owner cuts versus the external ordinary ledger

An owner-fibre cut has two pieces: edges leaving the whole residual set and
edges crossing to the other owner *inside* the residual set.  The latter
piece occurs in both Boolean owner equations.  Hence the discrepancy between
owner-resolved cut characters and the external ordinary ledger is exactly one
shared diagonal correction, not an uncontrolled pair of owner errors.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The external cut mass belonging to one residual owner fibre. -/
def ownerExternalCutMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) (R : Finset V) (owner : V → Bool)
    (i : Bool) : ZMod 2 :=
  ∑ y ∈ ownerWitnessCells R owner i,
    ∑ z ∈ ordinaryWitnessComplement R, graphEdgeIndicator W y z

/-- The internal cross-owner mass, oriented from false to true. -/
def residualCrossOwnerMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) (R : Finset V) (owner : V → Bool) : ZMod 2 :=
  ∑ y ∈ ownerWitnessCells R owner false,
    ∑ z ∈ ownerWitnessCells R owner true, graphEdgeIndicator W y z

private theorem complement_ownerFalse_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (owner : V → Bool) :
    ordinaryWitnessComplement (ownerWitnessCells R owner false) =
      ownerWitnessCells R owner true ∪ ordinaryWitnessComplement R := by
  ext z
  simp only [ordinaryWitnessComplement, ownerWitnessCells,
    Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter,
    Finset.mem_union]
  by_cases hz : z ∈ R <;> cases ho : owner z <;> simp [hz, ho]

private theorem complement_ownerTrue_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (owner : V → Bool) :
    ordinaryWitnessComplement (ownerWitnessCells R owner true) =
      ownerWitnessCells R owner false ∪ ordinaryWitnessComplement R := by
  ext z
  simp only [ordinaryWitnessComplement, ownerWitnessCells,
    Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter,
    Finset.mem_union]
  by_cases hz : z ∈ R <;> cases ho : owner z <;> simp [hz, ho]

private theorem ownerWitnessCells_disjoint_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (owner : V → Bool) (i : Bool) :
    Disjoint (ownerWitnessCells R owner i) (ordinaryWitnessComplement R) := by
  refine Finset.disjoint_left.mpr ?_
  intro z hzOwner hzOutside
  have hzR := (Finset.mem_filter.mp hzOwner).1
  exact (Finset.mem_sdiff.mp hzOutside).2 hzR

private theorem reverse_residualCrossOwnerMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj]
    (R : Finset V) (owner : V → Bool) :
    (∑ y ∈ ownerWitnessCells R owner true,
      ∑ z ∈ ownerWitnessCells R owner false, graphEdgeIndicator W y z) =
      residualCrossOwnerMass W R owner := by
  unfold residualCrossOwnerMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  simp [graphEdgeIndicator, W.adj_comm]

/-- The false-owner cut equals its external ledger mass plus the common
internal cross-owner correction. -/
theorem ownerFalse_cutMass_eq_external_add_crossOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj]
    (R : Finset V) (owner : V → Bool) :
    (graphCutMass W (ownerWitnessCells R owner false) : ZMod 2) =
      ownerExternalCutMass W R owner false +
        residualCrossOwnerMass W R owner := by
  rw [graphCutMass_cast_eq_sum_indicator_complement]
  rw [complement_ownerFalse_partition]
  unfold ownerExternalCutMass residualCrossOwnerMass
  simp_rw [Finset.sum_union
    (ownerWitnessCells_disjoint_complement R owner true)]
  rw [Finset.sum_add_distrib]
  abel

/-- The true-owner cut has the same diagonal correction. -/
theorem ownerTrue_cutMass_eq_external_add_crossOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj]
    (R : Finset V) (owner : V → Bool) :
    (graphCutMass W (ownerWitnessCells R owner true) : ZMod 2) =
      ownerExternalCutMass W R owner true +
        residualCrossOwnerMass W R owner := by
  rw [graphCutMass_cast_eq_sum_indicator_complement]
  rw [complement_ownerTrue_partition]
  unfold ownerExternalCutMass
  simp_rw [Finset.sum_union
    (ownerWitnessCells_disjoint_complement R owner false)]
  rw [Finset.sum_add_distrib]
  rw [reverse_residualCrossOwnerMass W R owner]
  abel

/-- Uniform two-owner form: both owner cuts differ from their external
ordinary ledgers by the same scalar diagonal correction. -/
theorem owner_cutMass_eq_external_add_crossOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj]
    (R : Finset V) (owner : V → Bool) (i : Bool) :
    (graphCutMass W (ownerWitnessCells R owner i) : ZMod 2) =
      ownerExternalCutMass W R owner i +
        residualCrossOwnerMass W R owner := by
  cases i
  · exact ownerFalse_cutMass_eq_external_add_crossOwner W R owner
  · exact ownerTrue_cutMass_eq_external_add_crossOwner W R owner

end

end Erdos85

#print axioms Erdos85.ownerFalse_cutMass_eq_external_add_crossOwner
#print axioms Erdos85.ownerTrue_cutMass_eq_external_add_crossOwner
#print axioms Erdos85.owner_cutMass_eq_external_add_crossOwner
