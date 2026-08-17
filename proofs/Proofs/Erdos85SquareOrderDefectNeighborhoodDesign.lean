import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85SquareOrderSectorProfile

/-!
# Original neighborhoods as a design on the defect complement

For a `C₄`-free graph, the neighborhoods of the original graph are not
arbitrary subsets of the second-order defect graph.  Each is defect-independent,
and every distinct defect nonedge lies in exactly one neighborhood.  At square
order the blocks all have size `d` or `d+1`.

This is the vertex-level structure absent from incidence-count and spectral
relaxations of the nonregular square-order problem.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def squareOrderDefectOwnerBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) : Finset V :=
  G.neighborFinset z

/-- Two distinct points in one original neighborhood cannot be adjacent in
the second-order defect graph. -/
theorem not_defectAdj_of_mem_squareOrderDefectOwnerBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {z u v : V}
    (hu : u ∈ squareOrderDefectOwnerBlock G z)
    (hv : v ∈ squareOrderDefectOwnerBlock G z) (huv : u ≠ v) :
    ¬ (secondOrderDefectGraph G).Adj u v := by
  intro hD
  have hzero :=
    (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree huv).mp hD
  have hzmem : z ∈ G.neighborFinset u ∩ G.neighborFinset v := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
        SimpleGraph.mem_neighborFinset] using hu
    · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
        SimpleGraph.mem_neighborFinset] using hv
  have hpos : 0 < (G.neighborFinset u ∩ G.neighborFinset v).card :=
    Finset.card_pos.mpr ⟨z, hzmem⟩
  omega

/-- Every distinct defect nonedge has a unique owner: its unique common
neighbor in the original graph. -/
theorem existsUnique_squareOrderDefectOwner_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {u v : V} (huv : u ≠ v)
    (hnot : ¬ (secondOrderDefectGraph G).Adj u v) :
    ∃! z : V, u ∈ squareOrderDefectOwnerBlock G z ∧
      v ∈ squareOrderDefectOwnerBlock G z := by
  have hcard := card_common_eq_if_secondOrderDefect G hfree u v huv
  have hnotmem :
      v ∉ (secondOrderDefectGraph G).neighborFinset u := by
    simpa [SimpleGraph.mem_neighborFinset] using hnot
  rw [if_neg hnotmem] at hcard
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hzmem : z ∈ G.neighborFinset u ∩ G.neighborFinset v := by
    rw [hz]
    simp
  refine ⟨z, ?_, ?_⟩
  · constructor
    · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
        SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hzmem).1
    · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
        SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hzmem).2
  · intro w hw
    have hwmem : w ∈ G.neighborFinset u ∩ G.neighborFinset v := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      constructor
      · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
          SimpleGraph.mem_neighborFinset] using hw.1
      · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
          SimpleGraph.mem_neighborFinset] using hw.2
    rw [hz] at hwmem
    simpa using hwmem

/-- Exact pair-design interface: distinct pairs are defect nonedges precisely
when they have a unique original-neighborhood owner. -/
theorem not_defectAdj_iff_existsUnique_squareOrderDefectOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {u v : V} (huv : u ≠ v) :
    ¬ (secondOrderDefectGraph G).Adj u v ↔
      ∃! z : V, u ∈ squareOrderDefectOwnerBlock G z ∧
        v ∈ squareOrderDefectOwnerBlock G z := by
  constructor
  · exact existsUnique_squareOrderDefectOwner_of_not_adj G hfree huv
  · rintro ⟨z, hz, _hunique⟩
    exact not_defectAdj_of_mem_squareOrderDefectOwnerBlock
      G hfree hz.1 hz.2 huv

/-- At square order every owner block has size `d` or `d+1`. -/
theorem squareOrder_card_defectOwnerBlock_eq_or_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (z : V) :
    (squareOrderDefectOwnerBlock G z).card = d ∨
      (squareOrderDefectOwnerBlock G z).card = d + 1 := by
  simpa [squareOrderDefectOwnerBlock, G.card_neighborFinset_eq_degree] using
    squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard z

end

end Erdos85
