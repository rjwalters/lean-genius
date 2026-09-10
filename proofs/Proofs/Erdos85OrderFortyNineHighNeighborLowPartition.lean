import Proofs.Erdos85OrderFortyNineSupportPartitions

/-! High-neighbor blocks exactly partition every chosen subset of low vertices. -/
namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem orderFortyNine_high_neighbor_low_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49)
    (E : Finset V) (hE : E ⊆ orderFortyNineLowVertices G)
    {h : V} (hh : h ∈ orderFortyNineHighVertices G) :
    (G.neighborFinset h).biUnion (fun x => G.neighborFinset x ∩ E) = E ∧
    (∀ x ∈ G.neighborFinset h, ∀ y ∈ G.neighborFinset h, x ≠ y →
      Disjoint (G.neighborFinset x ∩ E) (G.neighborFinset y ∩ E)) := by
  classical
  have hcover (v : V) (hv : v ∈ E) :
      ∃! x, x ∈ G.neighborFinset h ∧ v ∈ G.neighborFinset x := by
    have hv7 : G.degree v = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard v with h7 | h8
      · exact h7
      · exact ((Finset.mem_sdiff.mp (hE hv)).2
          (by simp [orderFortyNineHighVertices,h8])).elim
    obtain ⟨x,hx,huniq⟩ := orderFortyNine_low_neighborhood_partitions_highs
      G hfree hmin hcard hv7 hh
    refine ⟨x, ⟨(G.mem_neighborFinset _ _).mpr hx.2.symm,
      (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hx.1).symm⟩, ?_⟩
    intro y hy
    apply huniq y
    exact ⟨(G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hy.2).symm,
      ((G.mem_neighborFinset _ _).mp hy.1).symm⟩
  constructor
  · apply Finset.ext
    intro v
    constructor
    · intro hv
      obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_inter.mp hx).2
    · intro hv
      obtain ⟨x,hx,_⟩ := hcover v hv
      exact Finset.mem_biUnion.mpr ⟨x,hx.1,Finset.mem_inter.mpr ⟨hx.2,hv⟩⟩
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro v hvx hvy
    obtain ⟨z,_,huniq⟩ := hcover v (Finset.mem_inter.mp hvx).2
    exact hxy ((huniq x ⟨hx,(Finset.mem_inter.mp hvx).1⟩).trans
      (huniq y ⟨hy,(Finset.mem_inter.mp hvy).1⟩).symm)


/-- The disjoint blocks have total size exactly the chosen low subset. -/
theorem orderFortyNine_high_neighbor_low_incidence_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49)
    (E : Finset V) (hE : E ⊆ orderFortyNineLowVertices G)
    {h : V} (hh : h ∈ orderFortyNineHighVertices G) :
    (∑ x ∈ G.neighborFinset h, (G.neighborFinset x ∩ E).card) = E.card := by
  classical
  obtain ⟨hcover,hdis⟩ := orderFortyNine_high_neighbor_low_partition G hfree hmin hcard E hE hh
  have hd : (↑(G.neighborFinset h) : Set V).Pairwise (fun x y =>
      Disjoint (G.neighborFinset x ∩ E) (G.neighborFinset y ∩ E)) := hdis
  have hc := Finset.card_biUnion hd
  rw [hcover] at hc
  exact hc.symm

end
end Erdos85
#print axioms Erdos85.orderFortyNine_high_neighbor_low_partition

#print axioms Erdos85.orderFortyNine_high_neighbor_low_incidence_sum
