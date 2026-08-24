import Proofs.Erdos85BinarySquareNoFullEmptySizeQCore

/-!
# Shore-local replication excludes an order-q full-empty core

Full lines have all their neighbors on the chosen shore, while empty lines
have none there.  Consequently the only nontrivial replication bounds are
the full-family bound on the shore and the empty-family bound off the shore.
This file upgrades those local bounds to the global interface consumed by
the size-`q` exceptional-core contradiction.
-/

open SimpleGraph

namespace Erdos85

/-- A full family whose replication is at most one on `S` has replication at
most one everywhere: outside `S` its incidence is zero. -/
theorem fullFamily_replicationAtMostOne_of_on_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (S full : Finset V)
    (hfull : ∀ x ∈ full, (G.neighborFinset x ∩ S).card = q)
    (hcap : ∀ v ∈ S, (G.neighborFinset v ∩ full).card ≤ 1) :
    ∀ v, (G.neighborFinset v ∩ full).card ≤ 1 := by
  intro v
  by_cases hvS : v ∈ S
  · exact hcap v hvS
  · have hempty : G.neighborFinset v ∩ full = ∅ := by
      ext x
      constructor
      · intro hx
        have hxData := Finset.mem_inter.mp hx
        have hxFull := hfull x hxData.2
        have hxDegree : (G.neighborFinset x).card = q := by
          rw [G.card_neighborFinset_eq_degree, hreg]
        have hline : G.neighborFinset x ∩ S = G.neighborFinset x := by
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          omega
        have hvNx : v ∈ G.neighborFinset x :=
          (G.mem_neighborFinset x v).mpr
            ((G.mem_neighborFinset v x).mp hxData.1).symm
        have hvInter : v ∈ G.neighborFinset x ∩ S := by
          rw [hline]
          exact hvNx
        exact (hvS (Finset.mem_inter.mp hvInter).2).elim
      · simp
    rw [hempty]
    simp

/-- An empty family whose replication is at most one off `S` has replication
at most one everywhere: on `S` its incidence is zero. -/
theorem emptyFamily_replicationAtMostOne_of_off_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S empty : Finset V)
    (hempty : ∀ x ∈ empty, (G.neighborFinset x ∩ S).card = 0)
    (hcap : ∀ v ∉ S, (G.neighborFinset v ∩ empty).card ≤ 1) :
    ∀ v, (G.neighborFinset v ∩ empty).card ≤ 1 := by
  intro v
  by_cases hvS : v ∈ S
  · have hzero : G.neighborFinset v ∩ empty = ∅ := by
      ext x
      constructor
      · intro hx
        have hxData := Finset.mem_inter.mp hx
        have hvNx : v ∈ G.neighborFinset x :=
          (G.mem_neighborFinset x v).mpr
            ((G.mem_neighborFinset v x).mp hxData.1).symm
        have : v ∈ G.neighborFinset x ∩ S :=
          Finset.mem_inter.mpr ⟨hvNx, hvS⟩
        have hcardZero := hempty x hxData.2
        rw [Finset.card_eq_zero.mp hcardZero] at this
        simp at this
      · simp
    rw [hzero]
    simp
  · exact hcap v hvS

/-- Full/empty exceptional families with their natural shore-local
replication bounds cannot form a size-`q` core at even binary-square degree. -/
theorem binarySquare_regular_no_fullEmpty_sizeQ_core_of_localCaps_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S full empty : Finset V)
    (hfull : ∀ x ∈ full, (G.neighborFinset x ∩ S).card = q)
    (hempty : ∀ x ∈ empty, (G.neighborFinset x ∩ S).card = 0)
    (hfullCap : ∀ v ∈ S, (G.neighborFinset v ∩ full).card ≤ 1)
    (hemptyCap : ∀ v ∉ S, (G.neighborFinset v ∩ empty).card ≤ 1)
    (hcoreCard : (full ∪ empty).card = q) : False := by
  exact binarySquare_regular_no_fullEmpty_sizeQ_core_of_even
    G hfree hq hqEven hreg hcard S full empty hfull hempty
    (fullFamily_replicationAtMostOne_of_on_shore G hreg S full hfull hfullCap)
    (emptyFamily_replicationAtMostOne_of_off_shore G S empty hempty hemptyCap)
    hcoreCard

end Erdos85

#print axioms Erdos85.fullFamily_replicationAtMostOne_of_on_shore
#print axioms Erdos85.emptyFamily_replicationAtMostOne_of_off_shore
#print axioms Erdos85.binarySquare_regular_no_fullEmpty_sizeQ_core_of_localCaps_of_even
