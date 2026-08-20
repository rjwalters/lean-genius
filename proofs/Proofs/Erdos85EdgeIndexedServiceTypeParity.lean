import Proofs.Erdos85MuNegThreeZeroFiveCrossServiceProfiles

/-! # Parity of same-type service transitions -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The aggregate number of same-type service neighbors is even: it is the
degree sum of the service graph induced on that shore-edge type. -/
theorem serviceNeighborShoreTypeCount_same_sum_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (p : ℕ) :
    Even (∑ a ∈ shoreTypeEdgeFinset R S p,
      serviceNeighborShoreTypeCount R Cedge a S p) := by
  classical
  let E := shoreTypeEdgeFinset R S p
  let D := Cedge.induce {a | a ∈ E}
  have hdeg (a : E) : D.degree a =
      serviceNeighborShoreTypeCount R Cedge a.1 S p := by
    rw [SimpleGraph.degree]
    unfold serviceNeighborShoreTypeCount
    calc
      (D.neighborFinset a).card =
          ((D.neighborFinset a).image Subtype.val).card := by
            symm
            exact Finset.card_image_of_injective _ Subtype.val_injective
      _ = ((Cedge.neighborFinset a.1).filter fun b ↦
          (b.1.toFinset ∩ S).card = p).card := by
            congr 1
            ext b
            simp [D, E, shoreTypeEdgeFinset,
              SimpleGraph.mem_neighborFinset]
  have hedge := SimpleGraph.sum_degrees_eq_twice_card_edges D
  have heven : Even (∑ a : E,
      serviceNeighborShoreTypeCount R Cedge a.1 S p) := by
    refine ⟨D.edgeFinset.card, ?_⟩
    calc
      (∑ a : E, serviceNeighborShoreTypeCount R Cedge a.1 S p) =
          ∑ a : E, D.degree a := by
            apply Finset.sum_congr rfl
            intro a ha
            exact (hdeg a).symm
      _ = 2 * D.edgeFinset.card := hedge
      _ = D.edgeFinset.card + D.edgeFinset.card := by omega
  have hatt := Finset.sum_attach E
    (fun a ↦ serviceNeighborShoreTypeCount R Cedge a S p)
  rw [← hatt]
  simpa using heven

end

end Erdos85

#print axioms Erdos85.serviceNeighborShoreTypeCount_same_sum_even
