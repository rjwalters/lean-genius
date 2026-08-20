import Proofs.Erdos85MuNegThreeZeroFiveServiceShoreTypeProfiles
import Proofs.Erdos85EdgeIndexedServiceCommonStarCount

/-! # Global handshake for service-edge shore types -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Exterior edges with exactly `t` endpoints in a chosen shore. -/
def shoreTypeEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (S : Finset V) (t : ℕ) : Finset R.edgeFinset :=
  Finset.univ.filter fun a ↦ (a.1.toFinset ∩ S).card = t

/-- Directed service adjacencies from shore type `p` to shore type `q`. -/
def serviceTypeTransitionPairFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (p q : ℕ) :
    Finset (R.edgeFinset × R.edgeFinset) :=
  ((shoreTypeEdgeFinset R S p).product (shoreTypeEdgeFinset R S q)).filter
    fun ab ↦ Cedge.Adj ab.1 ab.2

private theorem card_filter_product_eq_sum_filter
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → β → Prop)
    [DecidableRel P] :
    ((s.product t).filter fun ab ↦ P ab.1 ab.2).card =
      ∑ a ∈ s, (t.filter fun b ↦ P a b).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ ab ∈ s ×ˢ t, if P ab.1 ab.2 then 1 else 0) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Undirectedness gives the global type-transition handshake: the number of
directed `p → q` service adjacencies equals the number of `q → p` ones. -/
theorem serviceTypeTransitionPairFinset_card_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (p q : ℕ) :
    (serviceTypeTransitionPairFinset R Cedge S p q).card =
      (serviceTypeTransitionPairFinset R Cedge S q p).card := by
  classical
  apply Finset.card_bij (fun ab _ ↦ (ab.2, ab.1))
  · intro ab hab
    rcases ab with ⟨a, b⟩
    have hab' := Finset.mem_filter.mp hab
    have htypes := Finset.mem_product.mp hab'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨htypes.2, htypes.1⟩,
      (Cedge.adj_comm a b).mp hab'.2⟩
  · intro ab hab cd hcd heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro ab hab
    rcases ab with ⟨a, b⟩
    refine ⟨(b, a), ?_, rfl⟩
    have hab' := Finset.mem_filter.mp hab
    have htypes := Finset.mem_product.mp hab'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨htypes.2, htypes.1⟩,
      (Cedge.adj_comm a b).mp hab'.2⟩

/-- Sum form of the global handshake, directly compatible with the local
`serviceNeighborShoreTypeCount` profiles. -/
theorem serviceNeighborShoreTypeCount_handshake
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (p q : ℕ) :
    (∑ a ∈ shoreTypeEdgeFinset R S p,
        serviceNeighborShoreTypeCount R Cedge a S q) =
      ∑ b ∈ shoreTypeEdgeFinset R S q,
        serviceNeighborShoreTypeCount R Cedge b S p := by
  classical
  let E (t : ℕ) := shoreTypeEdgeFinset R S t
  have hcount (r s : ℕ) :
      (serviceTypeTransitionPairFinset R Cedge S r s).card =
        ∑ a ∈ E r, serviceNeighborShoreTypeCount R Cedge a S s := by
    rw [serviceTypeTransitionPairFinset,
      card_filter_product_eq_sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    ext b
    simp [shoreTypeEdgeFinset, SimpleGraph.mem_neighborFinset, and_comm]
  rw [← hcount p q, serviceTypeTransitionPairFinset_card_comm,
    hcount q p]

end

end Erdos85

#print axioms Erdos85.serviceTypeTransitionPairFinset_card_comm
#print axioms Erdos85.serviceNeighborShoreTypeCount_handshake
