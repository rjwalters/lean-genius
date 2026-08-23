import Proofs.Erdos85OddSquareOrderNineArticulationLowSetTransfer

/-!
# The order-eighteen excess-two spike reduction

Node: B.3 / symmetric `(18,59)` articulation branch, audit equations
(29)--(32).

This file isolates the finite terminal after the excess-two defect-transfer
calculation.  There are three distinct bin-one partners of the bin-three
owner.  In the high-spike profile they all lie in the low set, contradicting
the owner low-set cap.  In the low-spike profile, equation (32) caps the
owner's low-set degree by one; the high-root transfer gives at least three
low-set partners when the spike center is bin zero and at least two when it
is bin one.  Hence the spike center must be the owner.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The high-spike high-root equation forces the spike center to be
high-free.  In cardinal form, equation (31) at a degree-ten high root says
that its `Z`-degree is `10 + 1_[h~c]`; the degree bound leaves no room for
the extra point. -/
theorem orderNine_order18_highSpike_center_not_adjacent_highRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) {h c : V}
    (hdeg : G.degree h = 10)
    (heq : (G.neighborFinset h ∩ Z).card =
      10 + if G.Adj h c then 1 else 0) :
    ¬ G.Adj h c := by
  intro hadj
  have hle : (G.neighborFinset h ∩ Z).card ≤ G.degree h := by
    simpa [G.card_neighborFinset_eq_degree] using
      Finset.card_le_card (Finset.inter_subset_left :
        G.neighborFinset h ∩ Z ⊆ G.neighborFinset h)
  rw [heq, if_pos hadj, hdeg] at hle
  omega

/-- Once the high-spike center is excluded from a high root, the same
high-root equation says that all ten neighbors of the root lie in `Z`. -/
theorem orderNine_order18_highSpike_highRoot_neighbors_subset_lowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) {h c : V}
    (hdeg : G.degree h = 10)
    (heq : (G.neighborFinset h ∩ Z).card =
      10 + if G.Adj h c then 1 else 0) :
    G.neighborFinset h ⊆ Z := by
  have hnadj := orderNine_order18_highSpike_center_not_adjacent_highRoot
    G Z hdeg heq
  have hcard : (G.neighborFinset h ∩ Z).card =
      (G.neighborFinset h).card := by
    rw [heq, if_neg hnadj, G.card_neighborFinset_eq_degree, hdeg]
  exact Finset.inter_eq_left.mp (Finset.eq_of_subset_of_card_le
    Finset.inter_subset_left (by omega :
      (G.neighborFinset h).card ≤ (G.neighborFinset h ∩ Z).card))

/-- **High-spike terminal.**  Three distinct owner partners cannot all lie
in a low set containing at most two owner-neighbors. -/
theorem false_of_orderNine_order18_highSpike_three_partners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (K Z : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hKZ : K ⊆ Z)
    (hownerZ : (G.neighborFinset owner ∩ Z).card ≤ 2) :
    False := by
  have hsub : K ⊆ G.neighborFinset owner ∩ Z := by
    intro y hy
    exact Finset.mem_inter.mpr ⟨hKowner hy, hKZ hy⟩
  have := Finset.card_le_card hsub
  omega

/-- Equation (32) always bounds the owner's low-set degree by one. -/
theorem orderNine_order18_lowSpike_owner_lowSet_degree_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (Z : Finset V)
    (heq32 : (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1) :
    (G.neighborFinset owner ∩ Z).card ≤ 1 := by
  split at heq32 <;> omega

/-- **Low-spike reduction.**  Let `K` be the three distinct bin-one
partners of the owner.  The high-root form of (31) supplies all three of
them in `Z` when the spike center is bin zero, and at least two when it is
bin one.  Equation (32) permits at most one.  Thus, among the exhaustive
possibilities `c=owner`, `c∈B₀`, and `c∈B₁`, only `c=owner` remains.

The two partner hypotheses are deliberately stated as the exact finite-set
outputs needed from the forthcoming graph-facing transfer wrapper. -/
theorem orderNine_order18_lowSpike_center_eq_owner_of_partner_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (K Z B₀ B₁ : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hcases : c = owner ∨ c ∈ B₀ ∨ c ∈ B₁)
    (hbinZero : c ∈ B₀ → K ⊆ Z)
    (hbinOne : c ∈ B₁ → 2 ≤ (K ∩ Z).card)
    (heq32 : (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1) :
    c = owner := by
  have hownerZ : (G.neighborFinset owner ∩ Z).card ≤ 1 :=
    orderNine_order18_lowSpike_owner_lowSet_degree_le_one
      G owner c Z heq32
  rcases hcases with rfl | hc0 | hc1
  · rfl
  · have hsub : K ⊆ G.neighborFinset owner ∩ Z := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨hKowner hy, hbinZero hc0 hy⟩
    have hle := Finset.card_le_card hsub
    omega
  · have hsub : K ∩ Z ⊆ G.neighborFinset owner ∩ Z := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨hKowner (Finset.mem_inter.mp hy).1,
        (Finset.mem_inter.mp hy).2⟩
    have hle := Finset.card_le_card hsub
    have htwo := hbinOne hc1
    omega

#print axioms Erdos85.orderNine_order18_highSpike_center_not_adjacent_highRoot
#print axioms Erdos85.orderNine_order18_highSpike_highRoot_neighbors_subset_lowSet
#print axioms Erdos85.false_of_orderNine_order18_highSpike_three_partners
#print axioms Erdos85.orderNine_order18_lowSpike_center_eq_owner_of_partner_bounds

end

end Erdos85
