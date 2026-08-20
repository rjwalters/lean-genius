import Proofs.Erdos85EdgeIndexedServiceShoreMass

/-! # Shore-type census for a service neighborhood -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Number of neighboring service edges having exactly `t` endpoints in `S`. -/
def serviceNeighborShoreTypeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (S : Finset V) (t : ℕ) : ℕ :=
  ((Cedge.neighborFinset a).filter fun b ↦
    (b.1.toFinset ∩ S).card = t).card

private theorem sum_eq_two_mul_filter_two_add_filter_one
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (hf : ∀ a ∈ s, f a ≤ 2) :
    ∑ a ∈ s, f a =
      2 * (s.filter fun a ↦ f a = 2).card +
        (s.filter fun a ↦ f a = 1).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ b ∈ s, f b ≤ 2 := by
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)
      have hi := ih hfs
      have hcases : f a = 0 ∨ f a = 1 ∨ f a = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · simp [Finset.sum_insert, Finset.filter_insert, ha, h0, hi]
      · simp [Finset.sum_insert, Finset.filter_insert, ha, h1, hi] <;> omega
      · simp [Finset.sum_insert, Finset.filter_insert, ha, h2, hi] <;> omega

private theorem card_eq_filter_zero_add_one_add_two
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (hf : ∀ a ∈ s, f a ≤ 2) :
    s.card = (s.filter fun a ↦ f a = 0).card +
      (s.filter fun a ↦ f a = 1).card +
      (s.filter fun a ↦ f a = 2).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ b ∈ s, f b ≤ 2 := by
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)
      have hi := ih hfs
      have hcases : f a = 0 ∨ f a = 1 ∨ f a = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · simp [Finset.filter_insert, ha, h0, hi] <;> omega
      · simp [Finset.filter_insert, ha, h1, hi] <;> omega
      · simp [Finset.filter_insert, ha, h2, hi] <;> omega

private theorem edge_endpoint_inter_card_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (b : R.edgeFinset) (S : Finset V) :
    (b.1.toFinset ∩ S).card ≤ 2 := by
  apply (Finset.card_le_card Finset.inter_subset_left).trans_eq
  exact Sym2.card_toFinset_of_not_isDiag b.1
    (R.not_isDiag_of_mem_edgeFinset b.2)

/-- The shore endpoint mass is `2·same + cross`, where the two counts are
defined intrinsically by the number of endpoints lying in the shore. -/
theorem edgeIndexedService_shoreMass_eq_typeCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (a : R.edgeFinset) (S : Finset V) :
    (serviceNeighborEndpointCover R Cedge a ∩ S).card =
      2 * serviceNeighborShoreTypeCount R Cedge a S 2 +
        serviceNeighborShoreTypeCount R Cedge a S 1 := by
  rw [← edgeIndexedService_sum_neighbor_endpoint_inter_card
    H R Cedge hservice a S]
  exact sum_eq_two_mul_filter_two_add_filter_one _ _ fun b _ ↦
    edge_endpoint_inter_card_le_two R b S

/-- The three possible shore endpoint types partition the service
neighborhood. -/
theorem edgeIndexedService_shoreTypeCounts_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (S : Finset V) :
    (Cedge.neighborFinset a).card =
      serviceNeighborShoreTypeCount R Cedge a S 0 +
      serviceNeighborShoreTypeCount R Cedge a S 1 +
      serviceNeighborShoreTypeCount R Cedge a S 2 := by
  exact card_eq_filter_zero_add_one_add_two _ _ fun b _ ↦
    edge_endpoint_inter_card_le_two R b S

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_shoreMass_eq_typeCounts
#print axioms Erdos85.edgeIndexedService_shoreTypeCounts_sum
