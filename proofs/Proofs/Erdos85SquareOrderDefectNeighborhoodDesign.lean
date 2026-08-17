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

def squareOrderDefectBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u z : V) : Finset V :=
  (G.neighborFinset z).erase u

def squareOrderDefectNonneighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  (Finset.univ.erase u) \ (secondOrderDefectGraph G).neighborFinset u

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

/-- Around a fixed point `u`, the punctured neighborhoods of its original
neighbors cover exactly the distinct defect nonneighbors of `u`. -/
theorem squareOrder_defectBranches_biUnion_eq_nonneighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (u : V) :
    (G.neighborFinset u).biUnion (squareOrderDefectBranch G u) =
      squareOrderDefectNonneighbors G u := by
  ext v
  constructor
  · intro hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨z, hzu, hvz⟩ := hv
    have hvne : v ≠ u := Finset.ne_of_mem_erase hvz
    have huz : u ∈ squareOrderDefectOwnerBlock G z := by
      simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset,
        G.adj_comm] using hzu
    have hvowner : v ∈ squareOrderDefectOwnerBlock G z := by
      exact Finset.mem_of_mem_erase hvz
    have hnot := not_defectAdj_of_mem_squareOrderDefectOwnerBlock
      G hfree huz hvowner hvne.symm
    simp [squareOrderDefectNonneighbors, hvne, hnot,
      SimpleGraph.mem_neighborFinset]
  · intro hv
    have hvdata : v ≠ u ∧ ¬ (secondOrderDefectGraph G).Adj u v := by
      simpa [squareOrderDefectNonneighbors, SimpleGraph.mem_neighborFinset]
        using hv
    obtain ⟨z, hz, _hunique⟩ :=
      existsUnique_squareOrderDefectOwner_of_not_adj
        G hfree hvdata.1.symm hvdata.2
    rw [Finset.mem_biUnion]
    refine ⟨z, ?_, ?_⟩
    · simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset,
        G.adj_comm] using hz.1
    · exact Finset.mem_erase.mpr ⟨hvdata.1, by
        simpa [squareOrderDefectOwnerBlock] using hz.2⟩

/-- The branches in the preceding cover are pairwise disjoint. -/
theorem squareOrder_defectBranches_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (u : V) :
    ∀ z ∈ G.neighborFinset u, ∀ w ∈ G.neighborFinset u,
      z ≠ w → Disjoint (squareOrderDefectBranch G u z)
        (squareOrderDefectBranch G u w) := by
  intro z hzu w hwu hzw
  rw [Finset.disjoint_left]
  intro v hvz hvw
  have hvz' : G.Adj z v := by
    simpa [squareOrderDefectBranch, SimpleGraph.mem_neighborFinset] using
      Finset.mem_of_mem_erase hvz
  have hvw' : G.Adj w v := by
    simpa [squareOrderDefectBranch, SimpleGraph.mem_neighborFinset] using
      Finset.mem_of_mem_erase hvw
  have hvu : v ≠ u := Finset.ne_of_mem_erase hvz
  have huz : G.Adj u z := by simpa [SimpleGraph.mem_neighborFinset] using hzu
  have huw : G.Adj u w := by simpa [SimpleGraph.mem_neighborFinset] using hwu
  exact hfree (containsC4_of_two_common hzw hvu.symm huz huw hvz'.symm hvw'.symm)

/-- A branch through an adjacent owner `z` has size `deg(z)-1`. -/
theorem card_squareOrderDefectBranch_eq_degree_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u z : V}
    (huz : G.Adj u z) :
    (squareOrderDefectBranch G u z).card = G.degree z - 1 := by
  have humem : u ∈ G.neighborFinset z := by
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using huz
  rw [squareOrderDefectBranch, Finset.card_erase_of_mem humem,
    G.card_neighborFinset_eq_degree]

/-- At square order a branch is large (size `d`) exactly when its owner is
high (degree `d+1`). -/
theorem squareOrder_card_defectBranch_eq_iff_owner_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {u z : V} (huz : G.Adj u z) :
    (squareOrderDefectBranch G u z).card = d ↔ G.degree z = d + 1 := by
  rw [card_squareOrderDefectBranch_eq_degree_sub_one G huz]
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard z with hz | hz <;> omega

/-- The incidence weight `k(u)` is exactly the number of large branches in
the local defect-nonneighbor partition at `u`. -/
theorem squareOrder_card_largeDefectBranches_eq_highIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (u : V) :
    ((G.neighborFinset u).filter fun z =>
        (squareOrderDefectBranch G u z).card = d).card =
      squareOrderHighIncidenceCount G d u := by
  unfold squareOrderHighIncidenceCount
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨huz, hbranch⟩
    exact ⟨huz, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (squareOrder_card_defectBranch_eq_iff_owner_high
        G hfree hd hmin hcover hcard huz).mp hbranch⟩⟩
  · rintro ⟨huz, hz⟩
    exact ⟨huz, (squareOrder_card_defectBranch_eq_iff_owner_high
      G hfree hd hmin hcover hcard huz).mpr (Finset.mem_filter.mp hz).2⟩

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
