import Proofs.Erdos85EdgeIndexedServiceTwoWalkCensus

/-! # Shore-weighted service two-walk mass -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Summing the incident two-walk mass over a vertex shore weights every
exterior edge by its number of endpoints in that shore. -/
theorem sum_incidentServiceTwoWalkMass_eq_endpointWeighted_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (a : R.edgeFinset) :
    (∑ u ∈ S, incidentServiceTwoWalkMass R Cedge u a) =
      ∑ b : R.edgeFinset,
        (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).card *
          (b.1.toFinset ∩ S).card := by
  classical
  unfold incidentServiceTwoWalkMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  let c := (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).card
  calc
    (∑ u ∈ S, if u ∈ b.1.toFinset then c else 0) =
        ∑ _u ∈ S.filter (· ∈ b.1.toFinset), c := by
          rw [Finset.sum_filter]
    _ = c * (b.1.toFinset ∩ S).card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have heq : S.filter (· ∈ b.1.toFinset) = b.1.toFinset ∩ S := by
        ext u
        simp [and_comm]
      rw [heq, mul_comm]
      simp

end

end Erdos85

#print axioms
  Erdos85.sum_incidentServiceTwoWalkMass_eq_endpointWeighted_common
