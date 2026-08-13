import Proofs.Erdos85OrderFortyNineHighBranchGeometry
import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85LocalTriangleParity
import Proofs.Erdos85OrderFortyNineDistOnePinning
import Proofs.Erdos85BranchDeficitSymmetry
import Proofs.Erdos85PairedBlockRigidity
import Proofs.Erdos85MinimumSectorAssemblyInterface
import Proofs.Erdos85SquareOrderHighRootKernel
import Proofs.Erdos85OrderFortyNineSquareRoot

/-!
# The two five-block systems in the order-49 one-high stratum

Around the unique high vertex, the forty leaves admit two partitions into
eight blocks of size five: the original-graph second-layer branches and the
second-order-defect owner fibers.  Their overlap matrix is the finite quotient
object for the remaining one-high analysis.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def orderFortyNineDefectOwnerFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s : {z : V // z ∈ G.neighborSet v}) : Finset V :=
  (secondOrderDefectGraph G).neighborFinset s.1

def orderFortyNineOneHighOverlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  (secondLayerBranch G v s ∩ orderFortyNineDefectOwnerFiber G v t).card

/-- Every defect-owner fiber centered in `N(v)` has five leaves. -/
theorem orderFortyNine_card_defectOwnerFiber_eq_five_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (orderFortyNineDefectOwnerFiber G v s).card = 5 := by
  have hs : s.1 ∈ G.neighborFinset v := by
    exact (G.mem_neighborFinset v s.1).2 s.2
  have hclosed :=
    orderFortyNine_card_closedDefectNeighborhood_eq_six_of_one_high
      G hfree hmin hcard hHigh hv hs
  have hnot : s.1 ∉ (secondOrderDefectGraph G).neighborFinset s.1 := by simp
  rw [Finset.card_insert_of_notMem hnot] at hclosed
  simpa [orderFortyNineDefectOwnerFiber] using hclosed

/-- Every original-graph branch has five leaves. -/
theorem orderFortyNine_card_originalBranch_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (secondLayerBranch G v s).card = 5 :=
  orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
    G hfree hmin hcard hv s

/-- Every overlap entry lies between zero and five. -/
theorem orderFortyNineOneHighOverlap_le_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineOneHighOverlap G v s t ≤ 5 := by
  apply le_trans (Finset.card_le_card Finset.inter_subset_left)
  exact (orderFortyNine_card_originalBranch_eq_five
    G hfree hmin hcard hv s).le

/-- Each original branch is partitioned by the eight defect-owner fibers. -/
theorem orderFortyNine_biUnion_branch_inter_ownerFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion
        (fun t => secondLayerBranch G v s ∩
          orderFortyNineDefectOwnerFiber G v t) =
      secondLayerBranch G v s := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨t, _, hyt⟩ := hy
    exact (Finset.mem_inter.mp hyt).1
  · intro hy
    have hyOutside : y ∉ insert v (G.neighborFinset v) :=
      (Finset.mem_sdiff.mp hy).2
    have hyv : y ≠ v := by
      intro h
      subst y
      exact hyOutside (by simp)
    have hvy : ¬ G.Adj v y := by
      intro h
      exact hyOutside (by
        simp [SimpleGraph.mem_neighborFinset, h])
    have hydeg : G.degree y = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard y with hy7 | hy8
      · exact hy7
      · have hvHigh : v ∈ orderFortyNineHighVertices G := by
          simp [orderFortyNineHighVertices, hv]
        have hyHigh : y ∈ orderFortyNineHighVertices G := by
          simp [orderFortyNineHighVertices, hy8]
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hHigh
        have hvw : v = w := by simpa [hw] using hvHigh
        have hyw : y = w := by simpa [hw] using hyHigh
        exact (hyv (hyw.trans hvw.symm)).elim
    obtain ⟨x, hx, _⟩ :=
      orderFortyNine_existsUnique_defectCenter_of_not_adj_high
        G hfree hmin hcard hv hydeg hvy
    let t : {z : V // z ∈ G.neighborSet v} :=
      ⟨x, (G.mem_neighborFinset v x).1 hx.1⟩
    rw [Finset.mem_biUnion]
    refine ⟨t, Finset.mem_univ t, Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
    exact ((secondOrderDefectGraph G).mem_neighborFinset x y).2 hx.2

/-- The intersections in the preceding branch decomposition are pairwise
disjoint. -/
theorem orderFortyNine_branch_inter_ownerFiber_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    ((Finset.univ : Finset {z : V // z ∈ G.neighborSet v}) :
      Set {z : V // z ∈ G.neighborSet v}).PairwiseDisjoint
      (fun t => secondLayerBranch G v s ∩
        orderFortyNineDefectOwnerFiber G v t) := by
  intro t _ u _ htu
  apply Finset.disjoint_left.mpr
  intro y hyt hyu
  have htOwner := (Finset.mem_inter.mp hyt).2
  have huOwner := (Finset.mem_inter.mp hyu).2
  have hpair := orderFortyNine_closedDefectNeighborhood_pairwiseDisjoint_at_high
    G hfree hmin hcard hv
  have htmem : t.1 ∈ (G.neighborFinset v : Set V) := by
    exact (G.mem_neighborFinset v t.1).2 t.2
  have humem : u.1 ∈ (G.neighborFinset v : Set V) := by
    exact (G.mem_neighborFinset v u.1).2 u.2
  have htune : t.1 ≠ u.1 := fun h => htu (Subtype.ext h)
  have hdisj := hpair htmem humem htune
  exact Finset.disjoint_left.mp hdisj
    (Finset.mem_insert.mpr (Or.inr htOwner))
    (Finset.mem_insert.mpr (Or.inr huOwner))

/-- Every row of the one-high overlap matrix sums to five. -/
theorem sum_orderFortyNineOneHighOverlap_row_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (∑ t, orderFortyNineOneHighOverlap G v s t) = 5 := by
  rw [← orderFortyNine_card_originalBranch_eq_five
      G hfree hmin hcard hv s,
    ← orderFortyNine_biUnion_branch_inter_ownerFiber
      G hfree hmin hcard hHigh hv s,
    Finset.card_biUnion
      (orderFortyNine_branch_inter_ownerFiber_pairwiseDisjoint
        G hfree hmin hcard hv s)]
  rfl

/-- Each defect-owner fiber is partitioned by the eight original branches. -/
theorem orderFortyNine_biUnion_branch_inter_ownerFiber_column
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (t : {z : V // z ∈ G.neighborSet v}) :
    (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion
        (fun s => secondLayerBranch G v s ∩
          orderFortyNineDefectOwnerFiber G v t) =
      orderFortyNineDefectOwnerFiber G v t := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨s, _, hys⟩ := hy
    exact (Finset.mem_inter.mp hys).2
  · intro hy
    have htmem : t.1 ∈ (G.neighborFinset v : Set V) := by
      exact (G.mem_neighborFinset v t.1).2 t.2
    have hyv : y ≠ v := by
      intro h
      subst y
      have hvDzero :=
        (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
          G hfree hmin hcard hv).1
      have hvDempty : (secondOrderDefectGraph G).neighborFinset v = ∅ := by
        rw [← Finset.card_eq_zero,
          (secondOrderDefectGraph G).card_neighborFinset_eq_degree, hvDzero]
      change v ∈ (secondOrderDefectGraph G).neighborFinset t.1 at hy
      have : t.1 ∈ (secondOrderDefectGraph G).neighborFinset v := by
        rw [SimpleGraph.mem_neighborFinset]
        exact (((secondOrderDefectGraph G).mem_neighborFinset t.1 v).1 hy).symm
      rw [hvDempty] at this
      exact Finset.notMem_empty _ this
    have hvy : ¬ G.Adj v y := by
      intro hvy
      let u : {z : V // z ∈ G.neighborSet v} := ⟨y, hvy⟩
      by_cases htu : t = u
      · have hty : t.1 = y := congrArg Subtype.val htu
        exact (secondOrderDefectGraph G).loopless.irrefl y
          (hty ▸ ((secondOrderDefectGraph G).mem_neighborFinset t.1 y).1 hy)
      · have hpair :=
          orderFortyNine_closedDefectNeighborhood_pairwiseDisjoint_at_high
            G hfree hmin hcard hv
        have humem : u.1 ∈ (G.neighborFinset v : Set V) := by
          exact (G.mem_neighborFinset v u.1).2 u.2
        have hdisj := hpair htmem humem (fun h => htu (Subtype.ext h))
        exact Finset.disjoint_left.mp hdisj
          (Finset.mem_insert.mpr (Or.inr hy))
          (Finset.mem_insert.mpr (Or.inl rfl))
    have hySecond : y ∈ secondLayer G v := by
      rw [orderFortyNine_secondLayer_degreeEight_eq_compl_closedNeighborhood
        G hfree hmin hcard hv]
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ y, by
          simp [SimpleGraph.mem_neighborFinset, hyv, hvy]⟩
    rw [secondLayer, Finset.mem_biUnion] at hySecond
    obtain ⟨s, _, hys⟩ := hySecond
    rw [Finset.mem_biUnion]
    exact ⟨s, Finset.mem_univ s, Finset.mem_inter.mpr ⟨hys, hy⟩⟩

/-- Every column of the one-high overlap matrix sums to five. -/
theorem sum_orderFortyNineOneHighOverlap_column_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (t : {z : V // z ∈ G.neighborSet v}) :
    (∑ s, orderFortyNineOneHighOverlap G v s t) = 5 := by
  have hpair := secondLayerBranch_pairwiseDisjoint G hfree v
  have hpairInter :
      ((Finset.univ : Finset {z : V // z ∈ G.neighborSet v}) :
        Set {z : V // z ∈ G.neighborSet v}).PairwiseDisjoint
        (fun s => secondLayerBranch G v s ∩
          orderFortyNineDefectOwnerFiber G v t) := by
    intro s _ u _ hsu
    apply Finset.disjoint_left.mpr
    intro y hys hyu
    exact Finset.disjoint_left.mp
      (hpair (Finset.mem_univ s) (Finset.mem_univ u) hsu)
      (Finset.mem_inter.mp hys).1 (Finset.mem_inter.mp hyu).1
  rw [← orderFortyNine_card_defectOwnerFiber_eq_five_of_one_high
      G hfree hmin hcard hHigh hv t,
    ← orderFortyNine_biUnion_branch_inter_ownerFiber_column
      G hfree hmin hcard hv t,
    Finset.card_biUnion hpairInter]
  rfl

/-- A local-matching partner cannot own any leaf in the other partner's
original branch.  The first center would be a common neighbor, whereas a
defect edge has zero common neighbors. -/
theorem orderFortyNineOneHighOverlap_eq_zero_of_centerAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {v : V} (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1) :
    orderFortyNineOneHighOverlap G v s t = 0 := by
  rw [orderFortyNineOneHighOverlap, Finset.card_eq_zero,
    Finset.eq_empty_iff_forall_notMem]
  intro y hy
  have hyParts := Finset.mem_inter.mp hy
  have hsy : G.Adj s.1 y := by
    exact (G.mem_neighborFinset s.1 y).1
      (Finset.mem_sdiff.mp hyParts.1).1
  have hDty : (secondOrderDefectGraph G).Adj t.1 y := by
    exact ((secondOrderDefectGraph G).mem_neighborFinset t.1 y).1 hyParts.2
  have hty : t.1 ≠ y := (secondOrderDefectGraph G).ne_of_adj hDty
  have hzero :=
    (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hty).1 hDty
  have hsCommon : s.1 ∈ G.neighborFinset t.1 ∩ G.neighborFinset y := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hst.symm, hsy.symm⟩
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hzero
  exact hzero s.1 hsCommon

/-- The diagonal overlap at a center is exactly the set of triangle-free
neighbors of that center. -/
theorem orderFortyNine_branch_inter_ownFiber_eq_triangleFreeNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    secondLayerBranch G v s ∩ orderFortyNineDefectOwnerFiber G v s =
      triangleFreeNeighbors G s.1 := by
  ext y
  constructor
  · intro hy
    have hyParts := Finset.mem_inter.mp hy
    have hsy : G.Adj s.1 y :=
      (G.mem_neighborFinset s.1 y).1 (Finset.mem_sdiff.mp hyParts.1).1
    have hDsy : (secondOrderDefectGraph G).Adj s.1 y :=
      ((secondOrderDefectGraph G).mem_neighborFinset s.1 y).1 hyParts.2
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree ((secondOrderDefectGraph G).ne_of_adj hDsy)).1 hDsy
    exact (mem_triangleFreeNeighbors G s.1 y).2 ⟨hsy, hzero⟩
  · intro hy
    have hyTF := (mem_triangleFreeNeighbors G s.1 y).1 hy
    have hsv : G.Adj s.1 v := s.2.symm
    have hyv : y ≠ v := by
      intro hyv
      subst y
      obtain ⟨z, hsz, hvz⟩ :=
        (orderFortyNine_existsUnique_local_partner_of_high
          G hfree hmin hcard hv hsv).exists
      have hzCommon : z ∈ G.neighborFinset s.1 ∩ G.neighborFinset v := by
        simp [SimpleGraph.mem_neighborFinset, hsz, hvz]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hyTF
      exact hyTF.2 z hzCommon
    have hvy : ¬ G.Adj v y := by
      intro hvy
      have hvCommon : v ∈ G.neighborFinset s.1 ∩ G.neighborFinset y := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
          SimpleGraph.mem_neighborFinset]
        exact ⟨hsv, hvy.symm⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hyTF
      exact hyTF.2 v hvCommon
    have hyBranch : y ∈ secondLayerBranch G v s := by
      exact Finset.mem_sdiff.mpr ⟨
        (G.mem_neighborFinset s.1 y).2 hyTF.1,
        by simp [SimpleGraph.mem_neighborFinset, hyv, hvy]⟩
    have hDsy : (secondOrderDefectGraph G).Adj s.1 y :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree (G.ne_of_adj hyTF.1)).2 hyTF.2
    exact Finset.mem_inter.mpr ⟨hyBranch,
      ((secondOrderDefectGraph G).mem_neighborFinset s.1 y).2 hDsy⟩

/-- Every diagonal entry of the one-high overlap matrix is odd. -/
theorem orderFortyNineOneHighOverlap_diag_mod_two_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineOneHighOverlap G v s s % 2 = 1 := by
  rw [orderFortyNineOneHighOverlap,
    orderFortyNine_branch_inter_ownFiber_eq_triangleFreeNeighbors
      G hfree hmin hcard hv s,
    triangleFreeNeighbors_card_mod_two_eq_vertexDegree G hfree]
  rw [orderFortyNine_neighbor_degree_seven_of_degreeEight
    G hfree hmin hcard hv s.2]

/-- Away from a locally matched pair of centers, common neighbors of a
center `t` and a leaf in branch `s` are exactly that leaf's neighbors in
branch `t`. -/
theorem orderFortyNine_common_center_leaf_eq_branch_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : ¬ G.Adj s.1 t.1) {y : V}
    (hy : y ∈ secondLayerBranch G v s) :
    G.neighborFinset t.1 ∩ G.neighborFinset y =
      G.neighborFinset y ∩ secondLayerBranch G v t := by
  ext z
  constructor
  · intro hz
    have hzParts := Finset.mem_inter.mp hz
    have htz : G.Adj t.1 z := (G.mem_neighborFinset t.1 z).1 hzParts.1
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).1 hzParts.2
    have hyOutside : y ∉ insert v (G.neighborFinset v) :=
      (Finset.mem_sdiff.mp hy).2
    have hzv : z ≠ v := by
      intro hzv
      subst z
      exact hyOutside (Finset.mem_insert.mpr (Or.inr
        ((G.mem_neighborFinset v y).2 hyz.symm)))
    have hzNotNv : z ∉ G.neighborFinset v := by
      intro hzNv
      have hvz : G.Adj v z := (G.mem_neighborFinset v z).1 hzNv
      have hsy : G.Adj s.1 y :=
        (G.mem_neighborFinset s.1 y).1 (Finset.mem_sdiff.mp hy).1
      by_cases hzs : z = s.1
      · subst z
        exact hst htz.symm
      · have hvy : v ≠ y := by
          intro hvy
          subst y
          exact hyOutside (by simp)
        exact hfree (containsC4_of_two_common hzs hvy
          hvz s.2 hyz hsy.symm)
    exact Finset.mem_inter.mpr ⟨hzParts.2,
      Finset.mem_sdiff.mpr ⟨hzParts.1, by
        simp [hzv, hzNotNv]⟩⟩
  · intro hz
    have hzParts := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr ⟨
      (Finset.mem_sdiff.mp hzParts.2).1, hzParts.1⟩

/-- For nonadjacent centers, an overlap entry is the corresponding directed
branch-miss count. -/
theorem orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : ¬ G.Adj s.1 t.1) :
    orderFortyNineOneHighOverlap G v s t = highBranchMissCount G v s t := by
  rw [orderFortyNineOneHighOverlap, highBranchMissCount]
  congr 1
  ext y
  constructor
  · intro hy
    have hyParts := Finset.mem_inter.mp hy
    have hDty : (secondOrderDefectGraph G).Adj t.1 y :=
      ((secondOrderDefectGraph G).mem_neighborFinset t.1 y).1 hyParts.2
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree
        ((secondOrderDefectGraph G).ne_of_adj hDty)).1 hDty
    have heq := orderFortyNine_common_center_leaf_eq_branch_neighbors
      G hfree s t hst hyParts.1
    rw [heq] at hzero
    exact Finset.mem_filter.mpr ⟨hyParts.1, hzero⟩
  · intro hy
    have hyParts := Finset.mem_filter.mp hy
    have heq := orderFortyNine_common_center_leaf_eq_branch_neighbors
      G hfree s t hst hyParts.1
    have hzero :
        (G.neighborFinset t.1 ∩ G.neighborFinset y).card = 0 := by
      rw [heq]
      exact hyParts.2
    have hty : t.1 ≠ y := by
      intro hty
      subst y
      exact (Finset.mem_sdiff.mp hyParts.1).2
        (Finset.mem_insert.mpr (Or.inr
          ((G.mem_neighborFinset v t.1).2 t.2)))
    have hDty : (secondOrderDefectGraph G).Adj t.1 y :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hty).2 hzero
    exact Finset.mem_inter.mpr ⟨hyParts.1,
      ((secondOrderDefectGraph G).mem_neighborFinset t.1 y).2 hDty⟩

/-- The one-high overlap matrix is symmetric away from locally matched
center pairs. -/
theorem orderFortyNineOneHighOverlap_comm_of_not_centerAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : ¬ G.Adj s.1 t.1) :
    orderFortyNineOneHighOverlap G v s t =
      orderFortyNineOneHighOverlap G v t s := by
  rw [orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
      G hfree s t hst,
    orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
      G hfree t s (by simpa [G.adj_comm] using hst)]
  exact highBranchMissCount_comm_of_equal_card G hfree s t
    ((orderFortyNine_card_originalBranch_eq_five
      G hfree hmin hcard hv s).trans
      (orderFortyNine_card_originalBranch_eq_five
        G hfree hmin hcard hv t).symm)

/-- The entire one-high overlap matrix is symmetric.  On matched center
pairs both directed entries vanish; all other entries are symmetric branch
miss counts. -/
theorem orderFortyNineOneHighOverlap_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineOneHighOverlap G v s t =
      orderFortyNineOneHighOverlap G v t s := by
  by_cases hst : G.Adj s.1 t.1
  · rw [orderFortyNineOneHighOverlap_eq_zero_of_centerAdj
      G hfree s t hst,
    orderFortyNineOneHighOverlap_eq_zero_of_centerAdj
      G hfree t s hst.symm]
  · exact orderFortyNineOneHighOverlap_comm_of_not_centerAdj
      G hfree hmin hcard hv s t hst

/-- The diagonal cannot be identically five.  Otherwise every branch is
independent, contradicting the clean unique-high obstruction. -/
theorem exists_orderFortyNineOneHighOverlap_diag_lt_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ s : {z : V // z ∈ G.neighborSet v},
      orderFortyNineOneHighOverlap G v s s < 5 := by
  by_contra hnone
  have hdiag : ∀ s : {z : V // z ∈ G.neighborSet v},
      orderFortyNineOneHighOverlap G v s s = 5 := by
    intro s
    have hle := orderFortyNineOneHighOverlap_le_five
      G hfree hmin hcard hv s s
    have hge : 5 ≤ orderFortyNineOneHighOverlap G v s s :=
      Nat.le_of_not_gt (fun hs => hnone ⟨s, hs⟩)
    omega
  have hunique : ∀ {w : V}, G.degree w = 8 → w = v := by
    intro w hw
    have hvMem : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hwMem : w ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hw]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hHigh
    have hvz : v = z := by simpa [hz] using hvMem
    have hwz : w = z := by simpa [hz] using hwMem
    exact hwz.trans hvz.symm
  have hcover : ∀ {x y : V}, G.Adj x y →
      G.degree x = 7 ∨ G.degree y = 7 := by
    intro x y hxy
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard x with hx7 | hx8
    · exact Or.inl hx7
    · rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard y with hy7 | hy8
      · exact Or.inr hy7
      · exact (orderFortyNine_not_adj_degreeEight_degreeEight
          G hfree hmin hcard hx8 hy8 hxy).elim
  have hclean : ∀ u : {z : V // z ∈ G.neighborSet v},
      ∀ {p q : V}, p ∈ secondLayerBranch G v u →
        q ∈ secondLayerBranch G v u → ¬ G.Adj p q := by
    intro u p q hp hq hpq
    have hinterCard :
        (secondLayerBranch G v u ∩
          orderFortyNineDefectOwnerFiber G v u).card = 5 := by
      simpa [orderFortyNineOneHighOverlap] using hdiag u
    have hbranchCard := orderFortyNine_card_originalBranch_eq_five
      G hfree hmin hcard hv u
    have hinterEq :
        secondLayerBranch G v u ∩
            orderFortyNineDefectOwnerFiber G v u =
          secondLayerBranch G v u := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      omega
    have hbranchTF : secondLayerBranch G v u =
        triangleFreeNeighbors G u.1 := by
      rw [← orderFortyNine_branch_inter_ownFiber_eq_triangleFreeNeighbors
        G hfree hmin hcard hv u, hinterEq]
    have hpTF : p ∈ triangleFreeNeighbors G u.1 := by
      rw [← hbranchTF]
      exact hp
    have hpData := (mem_triangleFreeNeighbors G u.1 p).1 hpTF
    have hqCommon : q ∈ G.neighborFinset u.1 ∩ G.neighborFinset p := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨
        (G.mem_neighborFinset u.1 q).1 (Finset.mem_sdiff.mp hq).1,
        hpq⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hpData
    exact hpData.2 q hqCommon
  exact false_of_squareOrder_uniqueHigh_clean
    G hfree (d := 7) (by omega) hmin hcover (by omega) (by omega) hunique hclean

/-- In fact every branch is dirty in the one-high stratum, so every odd
diagonal overlap entry is at most three. -/
theorem orderFortyNineOneHighOverlap_diag_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineOneHighOverlap G v s s ≤ 3 := by
  have hstructure := squareOrder_degree_succ_highRoot_structure
    G hfree (d := 7) (by omega) hmin (by omega) (by omega)
  have hneigh := hstructure.2.1
  have hlocal := hstructure.2.2
  have hexternal := externalRepairCandidates_eq_empty_of_squareOrder_highRoot
    G hfree (d := 7) (by omega) (by omega) (by omega) hneigh hlocal
  have hunique : ∀ {w : V}, G.degree w = 8 → w = v := by
    intro w hw
    have hvMem : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hwMem : w ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hw]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hHigh
    have hvz : v = z := by simpa [hz] using hvMem
    have hwz : w = z := by simpa [hz] using hwMem
    exact hwz.trans hvz.symm
  have houterDegree : ∀ {a : V}, a ∈ secondLayer G v →
      G.degree a = 7 := by
    intro a ha
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard a with ha7 | ha8
    · exact ha7
    · have hav := hunique ha8
      subst a
      rw [secondLayer] at ha
      rcases Finset.mem_biUnion.mp ha with ⟨u, _, hvBranch⟩
      exact ((Finset.mem_sdiff.mp hvBranch).2 (by simp)).elim
  obtain ⟨tval, hst, hvt⟩ :=
    (orderFortyNine_existsUnique_local_partner_of_high
      G hfree hmin hcard hv s.2.symm).exists
  let t : {z : V // z ∈ G.neighborSet v} := ⟨tval, hvt⟩
  have hmatched : 2 ≤ highBranchMatchedCount G v s :=
    (two_le_highBranchMatchedCount_of_paired_odd
      G hfree (d := 7) (by omega) (by norm_num [Odd])
      (by omega) hneigh hlocal hexternal houterDegree s t hst).1
  have hpartition := selfMiss_add_matchedCount_eq_five
    G hfree hmin hcard hv s
  rw [← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
    G hfree s s (G.loopless.irrefl s.1)] at hpartition
  omega

/-- Diagonal mass on a locally matched center pair is at most four.  Thus
the two endpoints of a local matching edge cannot both have diagonal three. -/
theorem orderFortyNineOneHighOverlap_paired_diag_sum_le_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1) :
    orderFortyNineOneHighOverlap G v s s +
      orderFortyNineOneHighOverlap G v t t ≤ 4 := by
  have hstructure := squareOrder_degree_succ_highRoot_structure
    G hfree (d := 7) (by omega) hmin (by omega) (by omega)
  have hneigh := hstructure.2.1
  have hlocal := hstructure.2.2
  have hexternal := externalRepairCandidates_eq_empty_of_squareOrder_highRoot
    G hfree (d := 7) (by omega) (by omega) (by omega) hneigh hlocal
  have hunique : ∀ {w : V}, G.degree w = 8 → w = v := by
    intro w hw
    have hvMem : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hwMem : w ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hw]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hHigh
    have hvz : v = z := by simpa [hz] using hvMem
    have hwz : w = z := by simpa [hz] using hwMem
    exact hwz.trans hvz.symm
  have houterDegree : ∀ {a : V}, a ∈ secondLayer G v →
      G.degree a = 7 := by
    intro a ha
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard a with ha7 | ha8
    · exact ha7
    · have hav := hunique ha8
      subst a
      rw [secondLayer] at ha
      rcases Finset.mem_biUnion.mp ha with ⟨u, _, hvBranch⟩
      exact ((Finset.mem_sdiff.mp hvBranch).2 (by simp)).elim
  have hmatched :=
    squareOrder_sub_one_le_add_matchedCounts_of_paired_of_odd
      G hfree (d := 7) (by omega) (by norm_num [Odd]) (by omega)
      hneigh hlocal hexternal houterDegree s t hst
  have hsPartition := selfMiss_add_matchedCount_eq_five
    G hfree hmin hcard hv s
  have htPartition := selfMiss_add_matchedCount_eq_five
    G hfree hmin hcard hv t
  rw [← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
    G hfree s s (G.loopless.irrefl s.1)] at hsPartition
  rw [← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
    G hfree t t (G.loopless.irrefl t.1)] at htPartition
  omega

/-- The paired outer-defect block is exactly the complement of the two
diagonal overlap masses.  This is the first exact compatibility equation
between the overlap matrix and the vertex-level outer defect graph. -/
theorem exists_orderFortyNine_mate_pairedDefect_add_overlapDiags_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ mate : {z : V // z ∈ G.neighborSet v} →
        {z : V // z ∈ G.neighborSet v},
      Function.Involutive mate ∧
      (∀ s, G.Adj s.1 (mate s).1) ∧
      ∀ s,
        (orderFortyNineOuterDefectBlock G v s (mate s)).card +
          orderFortyNineOneHighOverlap G v s s +
          orderFortyNineOneHighOverlap G v (mate s) (mate s) = 5 := by
  have hunique : ∀ {w : V}, G.degree w = 8 → w = v := by
    intro w hw
    have hvMem : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hwMem : w ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hw]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hHigh
    have hvz : v = z := by simpa [hz] using hvMem
    have hwz : w = z := by simpa [hz] using hwMem
    exact hwz.trans hvz.symm
  obtain ⟨mate, hmateInv, hmateAdj, hblocks⟩ :=
    orderFortyNine_exists_mate_exact_outerDefectBlocks
      G hfree hmin hcard hv hunique
  refine ⟨mate, hmateInv, hmateAdj, ?_⟩
  intro s
  have hblock := (hblocks s).1
  have hsPartition := selfMiss_add_matchedCount_eq_five
    G hfree hmin hcard hv s
  have hmPartition := selfMiss_add_matchedCount_eq_five
    G hfree hmin hcard hv (mate s)
  rw [← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
    G hfree s s (G.loopless.irrefl s.1)] at hsPartition
  rw [← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
    G hfree (mate s) (mate s) (G.loopless.irrefl (mate s).1)] at hmPartition
  omega

/-- In a one-regular local neighborhood, adjacency identifies the chosen
mate. -/
theorem eq_mate_of_local_centerAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1) :
    t = mate s := by
  have hcard := hlocal s
  rw [← (G.induce (G.neighborSet v)).card_neighborFinset_eq_degree,
    Finset.card_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  have htMem : t ∈ (G.induce (G.neighborSet v)).neighborFinset s :=
    ((G.induce (G.neighborSet v)).mem_neighborFinset s t).2 hst
  have hmMem : mate s ∈ (G.induce (G.neighborSet v)).neighborFinset s :=
    ((G.induce (G.neighborSet v)).mem_neighborFinset s (mate s)).2
      (hmateAdj s)
  have htx : t = x := by simpa [hx] using htMem
  have hmx : mate s = x := by simpa [hx] using hmMem
  exact htx.trans hmx.symm

/-- Full exact outer-defect compatibility in overlap coordinates. -/
theorem exists_orderFortyNine_mate_exact_outerDefect_overlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ mate : {z : V // z ∈ G.neighborSet v} →
        {z : V // z ∈ G.neighborSet v},
      Function.Involutive mate ∧
      (∀ s, G.Adj s.1 (mate s).1) ∧
      ∀ s,
        ((orderFortyNineOuterDefectBlock G v s (mate s)).card +
          orderFortyNineOneHighOverlap G v s s +
          orderFortyNineOneHighOverlap G v (mate s) (mate s) = 5) ∧
        ∀ u ∈ ((Finset.univ.erase s).erase (mate s)),
          (orderFortyNineOuterDefectBlock G v s u).card +
            orderFortyNineOneHighOverlap G v s (mate u) +
            orderFortyNineOneHighOverlap G v u (mate s) = 5 := by
  have hunique : ∀ {w : V}, G.degree w = 8 → w = v := by
    intro w hw
    have hvMem : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hwMem : w ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hw]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hHigh
    have hvz : v = z := by simpa [hz] using hvMem
    have hwz : w = z := by simpa [hz] using hwMem
    exact hwz.trans hvz.symm
  obtain ⟨mate, hmateInv, hmateAdj, hblocks⟩ :=
    orderFortyNine_exists_mate_exact_outerDefectBlocks
      G hfree hmin hcard hv hunique
  have hlocal := orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
    G hfree hmin hcard hv
  refine ⟨mate, hmateInv, hmateAdj, ?_⟩
  intro s
  constructor
  · have hblock := (hblocks s).1
    have hsPartition := selfMiss_add_matchedCount_eq_five
      G hfree hmin hcard hv s
    have hmPartition := selfMiss_add_matchedCount_eq_five
      G hfree hmin hcard hv (mate s)
    rw [← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
      G hfree s s (G.loopless.irrefl s.1)] at hsPartition
    rw [← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
      G hfree (mate s) (mate s) (G.loopless.irrefl (mate s).1)] at hmPartition
    omega
  · intro u hu
    have hus : u ≠ s := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hu).2).1
    have hsMateU : ¬ G.Adj s.1 (mate u).1 := by
      intro hsMu
      have heq := eq_mate_of_local_centerAdj
        G mate hmateAdj hlocal s (mate u) hsMu
      have hsu : s = u := by
        have := congrArg mate heq
        rw [hmateInv u, hmateInv s] at this
        exact this.symm
      exact hus hsu.symm
    have huMateS : ¬ G.Adj u.1 (mate s).1 := by
      intro huMs
      have heq := eq_mate_of_local_centerAdj
        G mate hmateAdj hlocal u (mate s) huMs
      have hus' : u = s := by
        have := congrArg mate heq
        rw [hmateInv s, hmateInv u] at this
        exact this.symm
      exact hus hus'
    have hfar := (hblocks s).2 u hu
    rw [← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
      G hfree s (mate u) hsMateU,
      ← orderFortyNineOneHighOverlap_eq_highBranchMissCount_of_not_centerAdj
        G hfree u (mate s) huMateS] at hfar
    exact hfar

/-- Number of vertices of a leaf-defect connected component carrying a
given defect-owner color. -/
def orderFortyNineLeafComponentOwnerCensus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  ((Finset.univ : Finset c.supp).filter fun y =>
    y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t).card

/-- The eight owner colors cover every leaf-defect component. -/
theorem orderFortyNine_biUnion_component_ownerColors_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent) :
    (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion
        (fun t => (Finset.univ : Finset c.supp).filter fun y =>
          y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t) =
      Finset.univ := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter,
    true_and]
  have hy7 : G.degree y.1.1 = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard y.1.1 with hy7 | hy8
    · exact hy7
    · have hyHigh : y.1.1 ∈ orderFortyNineHighVertices G := by
        simp [orderFortyNineHighVertices, hy8]
      have hvHigh : v ∈ orderFortyNineHighVertices G := by
        simp [orderFortyNineHighVertices, hv]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hHigh
      have hyv : y.1.1 = v := by
        have hyw : y.1.1 = w := by simpa [hw] using hyHigh
        have hvw : v = w := by simpa [hw] using hvHigh
        exact hyw.trans hvw.symm
      exact (y.1.2.1 hyv).elim
  obtain ⟨x, hx, _⟩ := orderFortyNine_existsUnique_defectCenter_of_not_adj_high
    G hfree hmin hcard hv hy7 y.1.2.2
  let t : {z : V // z ∈ G.neighborSet v} :=
    ⟨x, (G.mem_neighborFinset v x).1 hx.1⟩
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨t, ((secondOrderDefectGraph G).mem_neighborFinset x y.1.1).2 hx.2⟩

/-- Owner-color classes inside a leaf-defect component are pairwise
disjoint. -/
theorem orderFortyNine_component_ownerColors_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent) :
    ((Finset.univ : Finset {z : V // z ∈ G.neighborSet v}) :
      Set {z : V // z ∈ G.neighborSet v}).PairwiseDisjoint
        (fun t => (Finset.univ : Finset c.supp).filter fun y =>
          y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t) := by
  intro t _ u _ htu
  apply Finset.disjoint_left.mpr
  intro y hyt hyu
  have htOwner := (Finset.mem_filter.mp hyt).2
  have huOwner := (Finset.mem_filter.mp hyu).2
  have hpair := orderFortyNine_closedDefectNeighborhood_pairwiseDisjoint_at_high
    G hfree hmin hcard hv
  have htmem : t.1 ∈ (G.neighborFinset v : Set V) := by
    exact (G.mem_neighborFinset v t.1).2 t.2
  have humem : u.1 ∈ (G.neighborFinset v : Set V) := by
    exact (G.mem_neighborFinset v u.1).2 u.2
  have htune : t.1 ≠ u.1 := fun h => htu (Subtype.ext h)
  exact Finset.disjoint_left.mp (hpair htmem humem htune)
    (Finset.mem_insert.mpr (Or.inr htOwner))
    (Finset.mem_insert.mpr (Or.inr huOwner))

/-- The eight local owner-color counts sum to the order of the component. -/
theorem sum_orderFortyNineLeafComponentOwnerCensus_eq_componentOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent) :
    (∑ t, orderFortyNineLeafComponentOwnerCensus G v c t) =
      Fintype.card c.supp := by
  rw [← Finset.card_univ,
    ← orderFortyNine_biUnion_component_ownerColors_eq_univ
      G hfree hmin hcard hHigh hv c,
    Finset.card_biUnion
      (orderFortyNine_component_ownerColors_pairwiseDisjoint
        G hfree hmin hcard hv c)]
  rfl

/-- No component can contain more than the five vertices of a global owner
fiber in any one color. -/
theorem orderFortyNineLeafComponentOwnerCensus_le_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (t : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineLeafComponentOwnerCensus G v c t ≤ 5 := by
  rw [← orderFortyNine_card_defectOwnerFiber_eq_five_of_one_high
    G hfree hmin hcard hHigh hv t]
  apply Finset.card_le_card_of_injOn (fun y : c.supp => y.1.1)
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · intro a ha b hb hab
    exact Subtype.ext (Subtype.ext hab)

/-- Globally, each owner color has total mass five across all leaf-defect
components. -/
theorem sum_orderFortyNineLeafComponentOwnerCensus_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (t : {z : V // z ∈ G.neighborSet v}) :
    (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
      orderFortyNineLeafComponentOwnerCensus G v c t) = 5 := by
  let S : Finset {y : V // y ≠ v ∧ ¬ G.Adj v y} :=
    Finset.univ.filter fun y =>
      y.1 ∈ orderFortyNineDefectOwnerFiber G v t
  have hScard : S.card = 5 := by
    rw [← orderFortyNine_card_defectOwnerFiber_eq_five_of_one_high
      G hfree hmin hcard hHigh hv t]
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      exact (Finset.mem_filter.mp hy).2
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro q hq
      have hcover := orderFortyNine_biUnion_branch_inter_ownerFiber_column
        G hfree hmin hcard hv t
      have hqUnion : q ∈
          (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion
            (fun s => secondLayerBranch G v s ∩
              orderFortyNineDefectOwnerFiber G v t) := by
        rw [hcover]
        exact hq
      rw [Finset.mem_biUnion] at hqUnion
      obtain ⟨s, _, hqs⟩ := hqUnion
      have hqBranch := (Finset.mem_inter.mp hqs).1
      have hqOutside := (Finset.mem_sdiff.mp hqBranch).2
      let y : {y : V // y ≠ v ∧ ¬ G.Adj v y} := ⟨q, by
        constructor
        · intro h
          subst q
          exact hqOutside (by simp)
        · intro hvq
          exact hqOutside (by
            simp [SimpleGraph.mem_neighborFinset, hvq])⟩
      refine ⟨y, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  have hreindex := sum_vertex_eq_sum_connectedComponent_supp
    (orderFortyNineLeafDefectGraph G v)
    (fun y => if y.1 ∈ orderFortyNineDefectOwnerFiber G v t then 1 else 0)
  have hglobal :
      (∑ y : {y : V // y ≠ v ∧ ¬ G.Adj v y},
        if y.1 ∈ orderFortyNineDefectOwnerFiber G v t then 1 else 0) = 5 := by
    change ((Finset.univ : Finset {y : V // y ≠ v ∧ ¬ G.Adj v y}).filter
      (fun y => y.1 ∈ orderFortyNineDefectOwnerFiber G v t)).card = 5 at hScard
    rw [Finset.card_filter] at hScard
    exact hScard
  calc
    (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
        orderFortyNineLeafComponentOwnerCensus G v c t) =
        ∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
          ∑ y : c.supp,
            if y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [orderFortyNineLeafComponentOwnerCensus, Finset.card_filter]
    _ = ∑ y : {y : V // y ≠ v ∧ ¬ G.Adj v y},
          if y.1 ∈ orderFortyNineDefectOwnerFiber G v t then 1 else 0 :=
      hreindex.symm
    _ = 5 := hglobal

/-- There are at most six leaf-defect connected components. -/
theorem orderFortyNine_card_leafDefect_components_le_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    Fintype.card (orderFortyNineLeafDefectGraph G v).ConnectedComponent ≤ 6 := by
  have hsum := sum_vertex_eq_sum_connectedComponent_supp
    (orderFortyNineLeafDefectGraph G v) (fun _ => (1 : ℕ))
  have hleaf := orderFortyNine_card_leafLayer_eq_forty G hcard hv
  have hsumOrder :
      (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
        Fintype.card c.supp) = 40 := by
    simpa [hleaf] using hsum.symm
  have hlower :
      (∑ _c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent, 6) ≤
        ∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
          Fintype.card c.supp := by
    apply Finset.sum_le_sum
    intro c _
    exact (orderFortyNine_leafDefect_component_order_even_and_six_le
      G hfree hmin hcard hHigh hv c).1
  have hconst :
      (∑ _c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent, 6) =
        6 * Fintype.card
          (orderFortyNineLeafDefectGraph G v).ConnectedComponent := by
    simp [Nat.mul_comm]
  rw [hconst, hsumOrder] at hlower
  omega

/-- Component-local count for an original branch. -/
def orderFortyNineLeafComponentBranchCensus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  ((Finset.univ : Finset c.supp).filter fun y =>
    y.1.1 ∈ secondLayerBranch G v s).card

/-- Joint component/branch/owner census refining the global overlap
matrix. -/
def orderFortyNineLeafComponentOverlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  ((Finset.univ : Finset c.supp).filter fun y =>
    y.1.1 ∈ secondLayerBranch G v s ∧
      y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t).card

/-- Summing the joint census over owners gives the component-local original
branch count. -/
theorem sum_orderFortyNineLeafComponentOverlap_owner_eq_branchCensus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (∑ t, orderFortyNineLeafComponentOverlap G v c s t) =
      orderFortyNineLeafComponentBranchCensus G v c s := by
  let F := fun t : {z : V // z ∈ G.neighborSet v} =>
    (Finset.univ : Finset c.supp).filter fun y =>
      y.1.1 ∈ secondLayerBranch G v s ∧
        y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t
  have hpair : ((Finset.univ : Finset {z : V // z ∈ G.neighborSet v}) :
      Set {z : V // z ∈ G.neighborSet v}).PairwiseDisjoint F := by
    intro t _ u _ htu
    apply Finset.disjoint_left.mpr
    intro y hyt hyu
    have ht := (Finset.mem_filter.mp hyt).2.2
    have hu := (Finset.mem_filter.mp hyu).2.2
    have hbase := orderFortyNine_component_ownerColors_pairwiseDisjoint
      G hfree hmin hcard hv c
    exact Finset.disjoint_left.mp (hbase (Finset.mem_univ t)
      (Finset.mem_univ u) htu)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
  have hunion :
      (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion F =
        (Finset.univ : Finset c.supp).filter fun y =>
          y.1.1 ∈ secondLayerBranch G v s := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_biUnion] at hy
      obtain ⟨t, _, hyt⟩ := hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hyt).2.1⟩
    · intro hy
      have howners := orderFortyNine_biUnion_component_ownerColors_eq_univ
        G hfree hmin hcard hHigh hv c
      have hyAll : y ∈
          (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion
            (fun t => (Finset.univ : Finset c.supp).filter fun z =>
              z.1.1 ∈ orderFortyNineDefectOwnerFiber G v t) := by
        rw [howners]
        exact Finset.mem_univ _
      rw [Finset.mem_biUnion] at hyAll ⊢
      obtain ⟨t, _, hyt⟩ := hyAll
      exact ⟨t, Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2,
          (Finset.mem_filter.mp hyt).2⟩⟩
  change (∑ t, (F t).card) =
    ((Finset.univ : Finset c.supp).filter fun y =>
      y.1.1 ∈ secondLayerBranch G v s).card
  rw [← Finset.card_biUnion hpair, hunion]

/-- Summing the joint census over leaf-defect components recovers the global
branch/owner overlap entry. -/
theorem sum_orderFortyNineLeafComponentOverlap_component_eq_overlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
      orderFortyNineLeafComponentOverlap G v c s t) =
        orderFortyNineOneHighOverlap G v s t := by
  let S : Finset {y : V // y ≠ v ∧ ¬ G.Adj v y} :=
    Finset.univ.filter fun y =>
      y.1 ∈ secondLayerBranch G v s ∧
        y.1 ∈ orderFortyNineDefectOwnerFiber G v t
  have hScard : S.card = orderFortyNineOneHighOverlap G v s t := by
    rw [orderFortyNineOneHighOverlap]
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      exact Finset.mem_inter.mpr (Finset.mem_filter.mp hy).2
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro q hq
      have hqParts := Finset.mem_inter.mp hq
      have hqOutside := (Finset.mem_sdiff.mp hqParts.1).2
      let y : {y : V // y ≠ v ∧ ¬ G.Adj v y} := ⟨q, by
        constructor
        · intro h
          subst q
          exact hqOutside (by simp)
        · intro hvq
          exact hqOutside (by simp [SimpleGraph.mem_neighborFinset, hvq])⟩
      refine ⟨y, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqParts⟩
  have hreindex := sum_vertex_eq_sum_connectedComponent_supp
    (orderFortyNineLeafDefectGraph G v)
    (fun y => if y.1 ∈ secondLayerBranch G v s ∧
      y.1 ∈ orderFortyNineDefectOwnerFiber G v t then 1 else 0)
  have hglobal :
      (∑ y : {y : V // y ≠ v ∧ ¬ G.Adj v y},
        if y.1 ∈ secondLayerBranch G v s ∧
          y.1 ∈ orderFortyNineDefectOwnerFiber G v t then 1 else 0) =
        orderFortyNineOneHighOverlap G v s t := by
    rw [← hScard]
    dsimp only [S]
    rw [Finset.card_filter]
  calc
    (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
        orderFortyNineLeafComponentOverlap G v c s t) =
        ∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
          ∑ y : c.supp, if y.1.1 ∈ secondLayerBranch G v s ∧
            y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [orderFortyNineLeafComponentOverlap, Finset.card_filter]
    _ = ∑ y : {y : V // y ≠ v ∧ ¬ G.Adj v y},
          if y.1 ∈ secondLayerBranch G v s ∧
            y.1 ∈ orderFortyNineDefectOwnerFiber G v t then 1 else 0 :=
      hreindex.symm
    _ = orderFortyNineOneHighOverlap G v s t := hglobal

/-- Summing the joint census over original branches gives the
component-local owner-color count. -/
theorem sum_orderFortyNineLeafComponentOverlap_branch_eq_ownerCensus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (t : {z : V // z ∈ G.neighborSet v}) :
    (∑ s, orderFortyNineLeafComponentOverlap G v c s t) =
      orderFortyNineLeafComponentOwnerCensus G v c t := by
  let F := fun s : {z : V // z ∈ G.neighborSet v} =>
    (Finset.univ : Finset c.supp).filter fun y =>
      y.1.1 ∈ secondLayerBranch G v s ∧
        y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t
  have hpair : ((Finset.univ : Finset {z : V // z ∈ G.neighborSet v}) :
      Set {z : V // z ∈ G.neighborSet v}).PairwiseDisjoint F := by
    intro s _ u _ hsu
    apply Finset.disjoint_left.mpr
    intro y hys hyu
    have hsBranch := (Finset.mem_filter.mp hys).2.1
    have huBranch := (Finset.mem_filter.mp hyu).2.1
    exact Finset.disjoint_left.mp
      (secondLayerBranch_pairwiseDisjoint G hfree v
        (Finset.mem_univ s) (Finset.mem_univ u) hsu)
      hsBranch huBranch
  have hunion :
      (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion F =
        (Finset.univ : Finset c.supp).filter fun y =>
          y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_biUnion] at hy
      obtain ⟨s, _, hys⟩ := hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hys).2.2⟩
    · intro hy
      have hySecond : y.1.1 ∈ secondLayer G v := by
        rw [orderFortyNine_secondLayer_degreeEight_eq_compl_closedNeighborhood
          G hfree hmin hcard hv]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
          simp [SimpleGraph.mem_neighborFinset, y.1.2.1, y.1.2.2]⟩
      rw [secondLayer, Finset.mem_biUnion] at hySecond
      obtain ⟨s, _, hys⟩ := hySecond
      rw [Finset.mem_biUnion]
      exact ⟨s, Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hys, (Finset.mem_filter.mp hy).2⟩⟩
  change (∑ s, (F s).card) =
    ((Finset.univ : Finset c.supp).filter fun y =>
      y.1.1 ∈ orderFortyNineDefectOwnerFiber G v t).card
  rw [← Finset.card_biUnion hpair, hunion]

/-- Leaves in the same original high-root branch are nonadjacent in the
leaf defect graph: their branch center is already a common neighbor in the
original graph. -/
theorem orderFortyNineLeafDefect_not_adj_of_same_originalBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {v : V} (s : {z : V // z ∈ G.neighborSet v})
    (x y : {z : V // z ≠ v ∧ ¬ G.Adj v z})
    (hx : x.1 ∈ secondLayerBranch G v s)
    (hy : y.1 ∈ secondLayerBranch G v s) :
    ¬ (orderFortyNineLeafDefectGraph G v).Adj x y := by
  intro hxy
  have hDxy : (secondOrderDefectGraph G).Adj x.1 y.1 := hxy
  have hzero :=
    (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree
      ((secondOrderDefectGraph G).ne_of_adj hDxy)).1 hDxy
  have hsCommon : s.1 ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨
      ((G.mem_neighborFinset s.1 x.1).1
        (Finset.mem_sdiff.mp hx).1).symm,
      ((G.mem_neighborFinset s.1 y.1).1
        (Finset.mem_sdiff.mp hy).1).symm⟩
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hzero
  exact hzero s.1 hsCommon

/-- Consequently each component-local original-branch class is an
independent set in the induced component graph. -/
theorem orderFortyNine_componentBranchCensus_isIndepSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {v : V}
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (orderFortyNineLeafDefectGraph G v).induce c.supp |>.IsIndepSet
      ((Finset.univ : Finset c.supp).filter fun y =>
        y.1.1 ∈ secondLayerBranch G v s : Set c.supp) := by
  intro x hx y hy hxy
  intro hadj
  exact orderFortyNineLeafDefect_not_adj_of_same_originalBranch
    G hfree s x.1 y.1 (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2 hadj

/-- An independent original-branch class occupies at most half of any
5-regular leaf-defect component. -/
theorem two_mul_orderFortyNineLeafComponentBranchCensus_le_componentOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s : {z : V // z ∈ G.neighborSet v}) :
    2 * orderFortyNineLeafComponentBranchCensus G v c s ≤
      Fintype.card c.supp := by
  let L := orderFortyNineLeafDefectGraph G v
  let H := L.induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun y =>
    y.1.1 ∈ secondLayerBranch G v s
  let T : Finset c.supp := Finset.univ \ S
  have hHreg : ∀ x : c.supp, H.degree x = 5 := by
    intro x
    rw [show H.degree x = L.degree x.1 by
      exact degree_induce_connectedComponent_supp L c x]
    exact orderFortyNine_leafDefectGraph_degree_eq_five_of_one_high
      G hfree hmin hcard hHigh hv x.1
  have hcrossS : ∀ x ∈ S, (H.neighborFinset x ∩ T).card = 5 := by
    intro x hx
    have heq : H.neighborFinset x ∩ T = H.neighborFinset x := by
      ext y
      constructor
      · exact fun hy => (Finset.mem_inter.mp hy).1
      · intro hy
        apply Finset.mem_inter.mpr
        refine ⟨hy, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        intro hyS
        have hxBranch := (Finset.mem_filter.mp hx).2
        have hyBranch := (Finset.mem_filter.mp hyS).2
        exact orderFortyNineLeafDefect_not_adj_of_same_originalBranch
          G hfree s x.1 y.1 hxBranch hyBranch
            ((H.mem_neighborFinset x y).1 hy)
    rw [heq, H.card_neighborFinset_eq_degree, hHreg]
  have hcrossT : ∀ y ∈ T, (H.neighborFinset y ∩ S).card ≤ 5 := by
    intro y _
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (by rw [H.card_neighborFinset_eq_degree, hHreg])
  have hcomm := sum_card_neighbor_inter_comm H S T
  have hleft : (∑ x ∈ S, (H.neighborFinset x ∩ T).card) = 5 * S.card := by
    calc
      (∑ x ∈ S, (H.neighborFinset x ∩ T).card) =
          ∑ _x ∈ S, 5 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hcrossS x hx
      _ = 5 * S.card := by simp [Nat.mul_comm]
  have hright : (∑ y ∈ T, (H.neighborFinset y ∩ S).card) ≤
      5 * T.card := by
    calc
      (∑ y ∈ T, (H.neighborFinset y ∩ S).card) ≤
          ∑ _y ∈ T, 5 := Finset.sum_le_sum hcrossT
      _ = 5 * T.card := by simp [Nat.mul_comm]
  have hST : 5 * S.card ≤ 5 * T.card := by omega
  have hTcard : T.card = Fintype.card c.supp - S.card := by
    dsimp only [T]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ S),
      Finset.card_univ]
  change 2 * S.card ≤ Fintype.card c.supp
  rw [hTcard] at hST
  omega

/-- In a component of order six, 5-regularity makes the component graph
complete, so every original-branch class has size at most one. -/
theorem orderFortyNineLeafComponentBranchCensus_le_one_of_order_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (hc : Fintype.card c.supp = 6)
    (s : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineLeafComponentBranchCensus G v c s ≤ 1 := by
  let L := orderFortyNineLeafDefectGraph G v
  let H := L.induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun y =>
    y.1.1 ∈ secondLayerBranch G v s
  change S.card ≤ 1
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  by_contra hxy
  have hHreg : ∀ z : c.supp, H.degree z = 5 := by
    intro z
    rw [show H.degree z = L.degree z.1 by
      exact degree_induce_connectedComponent_supp L c z]
    exact orderFortyNine_leafDefectGraph_degree_eq_five_of_one_high
      G hfree hmin hcard hHigh hv z.1
  have hneighbors : H.neighborFinset x = Finset.univ.erase x := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      exact Finset.mem_erase.mpr ⟨
        (H.ne_of_adj ((H.mem_neighborFinset x z).1 hz)).symm,
        Finset.mem_univ _⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ x),
        Finset.card_univ, hc, H.card_neighborFinset_eq_degree, hHreg]
  have hAdj : H.Adj x y := by
    rw [← H.mem_neighborFinset, hneighbors]
    exact Finset.mem_erase.mpr ⟨fun h => hxy h.symm, Finset.mem_univ _⟩
  exact orderFortyNineLeafDefect_not_adj_of_same_originalBranch
    G hfree s x.1 y.1 (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2 hAdj

/-- Sharper component bound: a nonempty independent branch class forces all
five neighbors of any one of its vertices into the complement.  The empty
case uses the universal component lower bound six. -/
theorem orderFortyNineLeafComponentBranchCensus_add_five_le_componentOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineLeafComponentBranchCensus G v c s + 5 ≤
      Fintype.card c.supp := by
  let L := orderFortyNineLeafDefectGraph G v
  let H := L.induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun y =>
    y.1.1 ∈ secondLayerBranch G v s
  let T : Finset c.supp := Finset.univ \ S
  change S.card + 5 ≤ Fintype.card c.supp
  by_cases hS : S = ∅
  · rw [hS, Finset.card_empty, zero_add]
    exact (orderFortyNine_leafDefect_component_order_even_and_six_le
      G hfree hmin hcard hHigh hv c).1.trans' (by omega)
  · have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨x, hx⟩ := hSnonempty
    have hHreg : H.degree x = 5 := by
      rw [show H.degree x = L.degree x.1 by
        exact degree_induce_connectedComponent_supp L c x]
      exact orderFortyNine_leafDefectGraph_degree_eq_five_of_one_high
        G hfree hmin hcard hHigh hv x.1
    have hsub : H.neighborFinset x ⊆ T := by
      intro y hy
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hyS
      exact orderFortyNineLeafDefect_not_adj_of_same_originalBranch
        G hfree s x.1 y.1 (Finset.mem_filter.mp hx).2
          (Finset.mem_filter.mp hyS).2 ((H.mem_neighborFinset x y).1 hy)
    have hfive : 5 ≤ T.card := by
      rw [← hHreg, ← H.card_neighborFinset_eq_degree]
      exact Finset.card_le_card hsub
    have hTcard : T.card = Fintype.card c.supp - S.card := by
      dsimp only [T]
      rw [Finset.card_sdiff,
        Finset.inter_eq_left.mpr (Finset.subset_univ S), Finset.card_univ]
    rw [hTcard] at hfive
    omega

/-- Globally, each original branch has total mass five across the
leaf-defect components. -/
theorem sum_orderFortyNineLeafComponentBranchCensus_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
      orderFortyNineLeafComponentBranchCensus G v c s) = 5 := by
  calc
    (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
        orderFortyNineLeafComponentBranchCensus G v c s) =
        ∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
          ∑ t, orderFortyNineLeafComponentOverlap G v c s t := by
      apply Finset.sum_congr rfl
      intro c _
      exact (sum_orderFortyNineLeafComponentOverlap_owner_eq_branchCensus
        G hfree hmin hcard hHigh hv c s).symm
    _ = ∑ t, ∑ c :
        (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
          orderFortyNineLeafComponentOverlap G v c s t := by
      rw [Finset.sum_comm]
    _ = ∑ t, orderFortyNineOneHighOverlap G v s t := by
      apply Finset.sum_congr rfl
      intro t _
      exact sum_orderFortyNineLeafComponentOverlap_component_eq_overlap
        G hfree hmin hcard hv s t
    _ = 5 := sum_orderFortyNineOneHighOverlap_row_eq_five
      G hfree hmin hcard hHigh hv s

/-- For vertices in distinct original branches, vanishing of the global
common-neighbor set is equivalent to vanishing inside the outer graph. -/
theorem orderFortyNine_crossBranch_globalCommon_zero_iff_outerCommon_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t)
    {x y : V} (hx : x ∈ secondLayerBranch G v s)
    (hy : y ∈ secondLayerBranch G v t) :
    let x' : {z : V // z ∈ secondLayer G v} := ⟨x, by
      rw [secondLayer, Finset.mem_biUnion]
      exact ⟨s, Finset.mem_univ _, hx⟩⟩
    let y' : {z : V // z ∈ secondLayer G v} := ⟨y, by
      rw [secondLayer, Finset.mem_biUnion]
      exact ⟨t, Finset.mem_univ _, hy⟩⟩
    (G.neighborFinset x ∩ G.neighborFinset y).card = 0 ↔
      ((squareOrderOuterGraph G v).neighborFinset x' ∩
        (squareOrderOuterGraph G v).neighborFinset y').card = 0 := by
  dsimp only
  rw [Finset.card_eq_zero, Finset.card_eq_zero]
  constructor
  · intro hglobal
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqx : G.Adj q.1 x := by
      exact (((squareOrderOuterGraph G v).mem_neighborFinset
        ⟨x, by rw [secondLayer, Finset.mem_biUnion]; exact ⟨s, by simp, hx⟩⟩ q).1
          (Finset.mem_inter.mp hq).1).symm
    have hqy : G.Adj q.1 y := by
      exact (((squareOrderOuterGraph G v).mem_neighborFinset
        ⟨y, by rw [secondLayer, Finset.mem_biUnion]; exact ⟨t, by simp, hy⟩⟩ q).1
          (Finset.mem_inter.mp hq).2).symm
    have hqGlobal : q.1 ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hqx.symm, hqy.symm⟩
    rw [hglobal] at hqGlobal
    exact Finset.notMem_empty _ hqGlobal
  · intro houter
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqx : G.Adj q x := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
        (Finset.mem_inter.mp hq).1
    have hqy : G.Adj q y := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
        (Finset.mem_inter.mp hq).2
    have hxOutside := (Finset.mem_sdiff.mp hx).2
    have hyOutside := (Finset.mem_sdiff.mp hy).2
    have hqv : q ≠ v := by
      intro hqv
      subst q
      exact hxOutside (Finset.mem_insert.mpr (Or.inr
        ((G.mem_neighborFinset v x).2 hqx)))
    have hqNotNv : q ∉ G.neighborFinset v := by
      intro hqNv
      let r : {z : V // z ∈ G.neighborSet v} :=
        ⟨q, (G.mem_neighborFinset v q).1 hqNv⟩
      have hxr : x ∈ secondLayerBranch G v r :=
        Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset q x).2 hqx, hxOutside⟩
      have hyr : y ∈ secondLayerBranch G v r :=
        Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset q y).2 hqy, hyOutside⟩
      have hrs : r = s := by
        by_contra hrs
        exact Finset.disjoint_left.mp
          (secondLayerBranch_pairwiseDisjoint G hfree v
            (Finset.mem_univ r) (Finset.mem_univ s) hrs) hxr hx
      have hrt : r = t := by
        by_contra hrt
        exact Finset.disjoint_left.mp
          (secondLayerBranch_pairwiseDisjoint G hfree v
            (Finset.mem_univ r) (Finset.mem_univ t) hrt) hyr hy
      exact hst (hrs.symm.trans hrt)
    have hqSecond : q ∈ secondLayer G v := by
      rw [orderFortyNine_secondLayer_degreeEight_eq_compl_closedNeighborhood
        G hfree hmin hcard hv]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        simp [SimpleGraph.mem_neighborFinset, hqv, hqNotNv]⟩
    let q' : {z : V // z ∈ secondLayer G v} := ⟨q, hqSecond⟩
    have hqOuter : q' ∈
        (squareOrderOuterGraph G v).neighborFinset
            ⟨x, by rw [secondLayer, Finset.mem_biUnion]; exact ⟨s, by simp, hx⟩⟩ ∩
          (squareOrderOuterGraph G v).neighborFinset
            ⟨y, by rw [secondLayer, Finset.mem_biUnion]; exact ⟨t, by simp, hy⟩⟩ := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hqx.symm, hqy.symm⟩
    rw [houter] at hqOuter
    exact Finset.notMem_empty _ hqOuter

/-- Across distinct original branches, the outer second-order defect graph
and the induced leaf defect graph have exactly the same adjacency relation. -/
theorem orderFortyNine_crossBranch_outerDefect_adj_iff_leafDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t)
    {x y : V} (hx : x ∈ secondLayerBranch G v s)
    (hy : y ∈ secondLayerBranch G v t) :
    let xOuter : {z : V // z ∈ secondLayer G v} := ⟨x, by
      rw [secondLayer, Finset.mem_biUnion]
      exact ⟨s, Finset.mem_univ _, hx⟩⟩
    let yOuter : {z : V // z ∈ secondLayer G v} := ⟨y, by
      rw [secondLayer, Finset.mem_biUnion]
      exact ⟨t, Finset.mem_univ _, hy⟩⟩
    let xLeaf : {z : V // z ≠ v ∧ ¬ G.Adj v z} := ⟨x, by
      have hout := (Finset.mem_sdiff.mp hx).2
      constructor
      · intro h; subst x; exact hout (by simp)
      · intro hvx; exact hout (by
          simp [SimpleGraph.mem_neighborFinset, hvx])⟩
    let yLeaf : {z : V // z ≠ v ∧ ¬ G.Adj v z} := ⟨y, by
      have hout := (Finset.mem_sdiff.mp hy).2
      constructor
      · intro h; subst y; exact hout (by simp)
      · intro hvy; exact hout (by
          simp [SimpleGraph.mem_neighborFinset, hvy])⟩
    (secondOrderDefectGraph (squareOrderOuterGraph G v)).Adj xOuter yOuter ↔
      (orderFortyNineLeafDefectGraph G v).Adj xLeaf yLeaf := by
  dsimp only
  let R := squareOrderOuterGraph G v
  letI : DecidableRel (antipodalGraph R).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph R).Adj := Classical.decRel _
  have hxy : x ≠ y := by
    intro hxy
    subst y
    exact Finset.disjoint_left.mp
      (secondLayerBranch_pairwiseDisjoint G hfree v
        (Finset.mem_univ s) (Finset.mem_univ t) hst) hx hy
  have hOuterNe :
      (⟨x, by rw [secondLayer, Finset.mem_biUnion]; exact ⟨s, by simp, hx⟩⟩ :
        {z : V // z ∈ secondLayer G v}) ≠
      ⟨y, by rw [secondLayer, Finset.mem_biUnion]; exact ⟨t, by simp, hy⟩⟩ :=
    fun h => hxy (congrArg Subtype.val h)
  rw [secondOrderDefectGraph_adj_iff_card_common_eq_zero
      R (squareOrderOuterGraph_not_containsC4 G hfree) hOuterNe]
  change _ ↔ (secondOrderDefectGraph G).Adj x y
  rw [secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree hxy]
  exact (orderFortyNine_crossBranch_globalCommon_zero_iff_outerCommon_zero
    G hfree hmin hcard hv s t hst hx hy).symm

/-- Ordered global-defect edges between two original high-root branches. -/
def orderFortyNineLeafDefectBranchBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) : Finset (V × V) :=
  (secondLayerBranch G v s ×ˢ secondLayerBranch G v t).filter fun xy =>
    (secondOrderDefectGraph G).Adj xy.1 xy.2

/-- On distinct branches, outer-defect block cardinality is exactly the
cross-branch leaf-defect edge count. -/
theorem card_orderFortyNineOuterDefectBlock_eq_leafDefectBranchBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t) :
    (orderFortyNineOuterDefectBlock G v s t).card =
      (orderFortyNineLeafDefectBranchBlock G v s t).card := by
  apply Finset.card_bij (fun xy _ => (xy.1.1, xy.2.1))
  · intro xy hxy
    have hmem := Finset.mem_filter.mp hxy
    have hprod := Finset.mem_product.mp hmem.1
    have hx := (Finset.mem_filter.mp hprod.1).2
    have hy := (Finset.mem_filter.mp hprod.2).2
    have hAdj :=
      (orderFortyNine_crossBranch_outerDefect_adj_iff_leafDefect_adj
        G hfree hmin hcard hv s t hst hx hy).1 hmem.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hAdj⟩
  · intro a ha b hb hab
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hab)
    · exact Subtype.ext (congrArg Prod.snd hab)
  · intro xy hxy
    have hmem := Finset.mem_filter.mp hxy
    have hprod := Finset.mem_product.mp hmem.1
    have hxSecond : xy.1 ∈ secondLayer G v := by
      rw [secondLayer, Finset.mem_biUnion]
      exact ⟨s, Finset.mem_univ _, hprod.1⟩
    have hySecond : xy.2 ∈ secondLayer G v := by
      rw [secondLayer, Finset.mem_biUnion]
      exact ⟨t, Finset.mem_univ _, hprod.2⟩
    let x' : {z : V // z ∈ secondLayer G v} := ⟨xy.1, hxSecond⟩
    let y' : {z : V // z ∈ secondLayer G v} := ⟨xy.2, hySecond⟩
    have hOuterAdj :=
      (orderFortyNine_crossBranch_outerDefect_adj_iff_leafDefect_adj
        G hfree hmin hcard hv s t hst hprod.1 hprod.2).2 hmem.2
    refine ⟨(x', y'), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprod.1⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprod.2⟩⟩,
      hOuterAdj⟩

/-- Exact mate rigidity expressed entirely with cross-branch edge counts of
the 5-regular leaf defect graph and overlap entries. -/
theorem exists_orderFortyNine_mate_exact_leafDefect_overlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ mate : {z : V // z ∈ G.neighborSet v} →
        {z : V // z ∈ G.neighborSet v},
      Function.Involutive mate ∧
      (∀ s, G.Adj s.1 (mate s).1) ∧
      ∀ s,
        ((orderFortyNineLeafDefectBranchBlock G v s (mate s)).card +
          orderFortyNineOneHighOverlap G v s s +
          orderFortyNineOneHighOverlap G v (mate s) (mate s) = 5) ∧
        ∀ u ∈ ((Finset.univ.erase s).erase (mate s)),
          (orderFortyNineLeafDefectBranchBlock G v s u).card +
            orderFortyNineOneHighOverlap G v s (mate u) +
            orderFortyNineOneHighOverlap G v u (mate s) = 5 := by
  obtain ⟨mate, hmateInv, hmateAdj, hrigid⟩ :=
    exists_orderFortyNine_mate_exact_outerDefect_overlap
      G hfree hmin hcard hHigh hv
  refine ⟨mate, hmateInv, hmateAdj, ?_⟩
  intro s
  have hmateNe : s ≠ mate s := by
    intro h
    exact G.loopless.irrefl s.1
      (congrArg Subtype.val h ▸ hmateAdj s)
  constructor
  · rw [← card_orderFortyNineOuterDefectBlock_eq_leafDefectBranchBlock
      G hfree hmin hcard hv s (mate s) hmateNe]
    exact (hrigid s).1
  · intro u hu
    have hsu : s ≠ u := by
      intro h
      subst u
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1 rfl
    rw [← card_orderFortyNineOuterDefectBlock_eq_leafDefectBranchBlock
      G hfree hmin hcard hv s u hsu]
    exact (hrigid s).2 u hu

/-- Directed leaf-defect incidences from original branch `s` to branch
`t`. -/
def orderFortyNineLeafDefectBranchIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  ∑ x : {z : V // z ≠ v ∧ ¬ G.Adj v z},
    if x.1 ∈ secondLayerBranch G v s then
      ((orderFortyNineLeafDefectGraph G v).neighborFinset x).filter
        (fun y => y.1 ∈ secondLayerBranch G v t) |>.card
    else 0

/-- Edges of a graph running between the open neighborhoods of two marked
vertices. -/
def neighborToNeighborEdgeBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (a b : V) : Finset (V × V) :=
  (H.neighborFinset a ×ˢ H.neighborFinset b).filter fun xy =>
    H.Adj xy.1 xy.2

/-- A length-three adjacency-matrix entry counts the edges between the two
endpoint neighborhoods. -/
theorem card_neighborToNeighborEdgeBlock_eq_adjMatrix_cube_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (a b : V) :
    (neighborToNeighborEdgeBlock H a b).card =
      (H.adjMatrix ℕ * H.adjMatrix ℕ * H.adjMatrix ℕ) a b := by
  rw [neighborToNeighborEdgeBlock, Finset.card_filter,
    Finset.sum_product, Matrix.mul_apply]
  simp only [SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_comm]
  calc
    (∑ y ∈ H.neighborFinset b,
        ∑ x ∈ H.neighborFinset a, if H.Adj x y then 1 else 0) =
        ∑ y, if H.Adj y b then
          (∑ x ∈ H.neighborFinset a, if H.Adj x y then 1 else 0)
        else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext y
      simp [SimpleGraph.mem_neighborFinset, H.adj_comm]
    _ = ∑ y, (H.adjMatrix ℕ * H.adjMatrix ℕ) a y *
          if H.Adj y b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hyb : H.Adj y b
      · simp only [if_pos hyb, Nat.mul_one]
        rw [Matrix.mul_apply]
        simp only [SimpleGraph.adjMatrix_apply]
        rw [neighborFinset_eq_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hax : H.Adj a x <;> by_cases hxy : H.Adj x y <;>
          simp [hax, hxy]
      · simp [hyb]

/-- The diagonal neighborhood-edge block has even cardinality: it is the
set of oriented edges of the graph induced on one neighborhood. -/
theorem even_card_neighborToNeighborEdgeBlock_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (a : V) :
    Even (neighborToNeighborEdgeBlock H a a).card := by
  let S := {x : V | H.Adj a x}
  let K := H.induce S
  let U : Finset (S × S) := Finset.univ.filter fun xy => K.Adj xy.1 xy.2
  have hcard : (neighborToNeighborEdgeBlock H a a).card = U.card := by
    apply Finset.card_bij
      (s := neighborToNeighborEdgeBlock H a a) (t := U)
      (fun xy hxy =>
        (⟨xy.1, by
            have hp := (Finset.mem_filter.mp hxy).1
            exact (H.mem_neighborFinset a xy.1).1
              (Finset.mem_product.mp hp).1⟩,
         ⟨xy.2, by
            have hp := (Finset.mem_filter.mp hxy).1
            exact (H.mem_neighborFinset a xy.2).1
              (Finset.mem_product.mp hp).2⟩))
    · intro xy hxy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hxy).2⟩
    · intro x _ y _ hxy
      exact Prod.ext
        (congrArg (fun z => z.1.1) hxy)
        (congrArg (fun z => z.2.1) hxy)
    · intro xy hxy
      refine ⟨(xy.1.1, xy.2.1), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
        (H.mem_neighborFinset a xy.1.1).2 xy.1.2,
        (H.mem_neighborFinset a xy.2.1).2 xy.2.2⟩,
        (Finset.mem_filter.mp hxy).2⟩
  have hU : 2 * K.edgeFinset.card = U.card := by
    exact K.two_mul_card_edgeFinset
  refine ⟨K.edgeFinset.card, ?_⟩
  omega

/-- Defect edges running between the two owner fibers centered at neighbors
`s,t` of the unique high root. -/
def orderFortyNineDefectOwnerEdgeBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) : Finset (V × V) :=
  neighborToNeighborEdgeBlock (secondOrderDefectGraph G) s.1 t.1

/-- The owner-fiber edge quotient is exactly the center block of the cube of
the full defect adjacency matrix. -/
theorem card_orderFortyNineDefectOwnerEdgeBlock_eq_defectCube_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    (orderFortyNineDefectOwnerEdgeBlock G v s t).card =
      ((secondOrderDefectGraph G).adjMatrix ℕ *
          (secondOrderDefectGraph G).adjMatrix ℕ *
          (secondOrderDefectGraph G).adjMatrix ℕ) s.1 t.1 := by
  exact card_neighborToNeighborEdgeBlock_eq_adjMatrix_cube_apply
    (secondOrderDefectGraph G) s.1 t.1

/-- Every diagonal owner-fiber edge count, equivalently every diagonal entry
of the defect cube on a center, is even. -/
theorem even_card_orderFortyNineDefectOwnerEdgeBlock_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s : {z : V // z ∈ G.neighborSet v}) :
    Even (orderFortyNineDefectOwnerEdgeBlock G v s s).card := by
  exact even_card_neighborToNeighborEdgeBlock_self
    (secondOrderDefectGraph G) s.1

/-- At order 49, the sum of neighbor degrees is the seven-regular baseline
plus the number of incident high vertices. -/
theorem orderFortyNine_sum_neighbor_degrees_eq_baseline_add_highIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) (x : V) :
    (∑ y ∈ G.neighborFinset x, G.degree y) =
      7 * G.degree x +
        (G.neighborFinset x ∩ orderFortyNineHighVertices G).card := by
  calc
    (∑ y ∈ G.neighborFinset x, G.degree y) =
        ∑ y ∈ G.neighborFinset x,
          (7 + if G.degree y = 8 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard y with hy | hy
      · simp [hy]
      · simp [hy]
    _ = 7 * G.degree x +
        ((G.neighborFinset x).filter fun y => G.degree y = 8).card := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_const, nsmul_eq_mul,
        G.card_neighborFinset_eq_degree, Finset.sum_boole]
      simp [Nat.mul_comm]
    _ = _ := by
      congr 1
      congr 1
      ext y
      simp [orderFortyNineHighVertices, and_comm]

/-- A center adjacent to the unique high vertex has neighbor-degree sum 50. -/
theorem orderFortyNine_sum_neighbor_degrees_center_eq_fifty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v s : V} (hv : G.degree v = 8) (hvs : G.Adj v s) :
    (∑ y ∈ G.neighborFinset s, G.degree y) = 50 := by
  have hsdeg := orderFortyNine_neighbor_degree_seven_of_degreeEight
    G hfree hmin hcard hv hvs
  have hvHigh : v ∈ orderFortyNineHighVertices G := by
    simp [orderFortyNineHighVertices, hv]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hHigh
  have hvw : v = w := by simpa [hw] using hvHigh
  have hHighEq : orderFortyNineHighVertices G = {v} := by
    simpa [hvw] using hw
  rw [orderFortyNine_sum_neighbor_degrees_eq_baseline_add_highIncidence
    G hfree hmin hcard, hsdeg, hHighEq]
  simp [SimpleGraph.mem_neighborFinset, hvs.symm]

/-- A low leaf not adjacent to the unique high vertex has neighbor-degree
sum 49. -/
theorem orderFortyNine_sum_neighbor_degrees_leaf_eq_fortyNine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v y : V} (hv : G.degree v = 8) (hy : G.degree y = 7)
    (hvy : ¬ G.Adj v y) :
    (∑ z ∈ G.neighborFinset y, G.degree z) = 49 := by
  have hvHigh : v ∈ orderFortyNineHighVertices G := by
    simp [orderFortyNineHighVertices, hv]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hHigh
  have hvw : v = w := by simpa [hw] using hvHigh
  have hHighEq : orderFortyNineHighVertices G = {v} := by
    simpa [hvw] using hw
  rw [orderFortyNine_sum_neighbor_degrees_eq_baseline_add_highIncidence
    G hfree hmin hcard, hy, hHighEq]
  simp [SimpleGraph.mem_neighborFinset, G.adj_comm, hvy]

/-- The row sum of `A²` is the sum of the degrees of the neighbors of the
row vertex. -/
theorem adjMatrix_sq_mul_onesMatrix_apply_eq_sum_neighbor_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ *
      FriendshipTheoremOQ01.onesMatrix V) x y =
        ∑ z ∈ G.neighborFinset x, (G.degree z : ℤ) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [adjMatrix_mul_onesMatrix_apply_eq_degree]
  rw [neighborFinset_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  simp only [SimpleGraph.adjMatrix_apply]
  by_cases hxz : G.Adj x z <;> simp [hxz]

/-- The column sum of `A²` is the same neighbor-degree sum, by symmetry. -/
theorem onesMatrix_mul_adjMatrix_sq_apply_eq_sum_neighbor_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (FriendshipTheoremOQ01.onesMatrix V * G.adjMatrix ℤ *
      G.adjMatrix ℤ) x y =
        ∑ z ∈ G.neighborFinset y, (G.degree z : ℤ) := by
  rw [Matrix.mul_apply]
  simp_rw [onesMatrix_mul_adjMatrix_apply_eq_degree]
  rw [neighborFinset_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  simp only [SimpleGraph.adjMatrix_apply]
  by_cases hyz : G.Adj y z <;> simp [hyz, G.adj_comm]

/-- Exact center-to-leaf fourth-walk formula in the one-high stratum.  It is
the center/leaf entry of the square of
`D = diag(degree-1) + J - A²`. -/
theorem orderFortyNine_defectSquare_center_leaf_eq_fourthWalk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v s y : V} (hv : G.degree v = 8) (hvs : G.Adj v s)
    (hy : G.degree y = 7) (hvy : ¬ G.Adj v y) :
    ((secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) s y =
      ((G.adjMatrix ℤ * G.adjMatrix ℤ) *
          (G.adjMatrix ℤ * G.adjMatrix ℤ)) s y - 38 -
        12 * (G.adjMatrix ℤ * G.adjMatrix ℤ) s y := by
  let A := G.adjMatrix ℤ
  let B := degreePredDiagonal G
  let J := FriendshipTheoremOQ01.onesMatrix V
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let M := A * A
  have hsdeg : G.degree s = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv hvs
  have hsy : s ≠ y := by
    intro h
    subst y
    exact hvy hvs
  have hD : D = B + J - M := by
    have hsq :=
      adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect
        G hfree
    dsimp [A, B, J, D, M]
    rw [hsq]
    noncomm_ring
  have hexpand :
      D * D = B * B + B * J + J * B - B * M - M * B +
        J * J - J * M - M * J + M * M := by
    rw [hD]
    noncomm_ring
  have hBB : (B * B) s y = 0 := by
    rw [show B = Matrix.diagonal (fun x => (G.degree x : ℤ) - 1) by
      rfl, Matrix.diagonal_mul_diagonal]
    simp [hsy]
  have hBJ : (B * J) s y = 6 := by
    rw [show B = Matrix.diagonal (fun x => (G.degree x : ℤ) - 1) by
      rfl, Matrix.diagonal_mul]
    simp [J, FriendshipTheoremOQ01.onesMatrix, hsdeg]
  have hJB : (J * B) s y = 6 := by
    rw [show B = Matrix.diagonal (fun x => (G.degree x : ℤ) - 1) by
      rfl, Matrix.mul_diagonal]
    simp [J, FriendshipTheoremOQ01.onesMatrix, hy]
  have hBM : (B * M) s y = 6 * M s y := by
    rw [show B = Matrix.diagonal (fun x => (G.degree x : ℤ) - 1) by
      rfl, Matrix.diagonal_mul]
    simp [hsdeg]
  have hMB : (M * B) s y = 6 * M s y := by
    rw [show B = Matrix.diagonal (fun x => (G.degree x : ℤ) - 1) by
      rfl, Matrix.mul_diagonal]
    simp [hy]
    ring
  have hJJ : (J * J) s y = 49 := by
    rw [Matrix.mul_apply]
    simp [J, FriendshipTheoremOQ01.onesMatrix, hcard]
  have hJM : (J * M) s y = 49 := by
    dsimp [J, M, A]
    rw [← Matrix.mul_assoc,
      onesMatrix_mul_adjMatrix_sq_apply_eq_sum_neighbor_degrees]
    exact_mod_cast orderFortyNine_sum_neighbor_degrees_leaf_eq_fortyNine
      G hfree hmin hcard hHigh hv hy hvy
  have hMJ : (M * J) s y = 50 := by
    dsimp [J, M, A]
    rw [adjMatrix_sq_mul_onesMatrix_apply_eq_sum_neighbor_degrees]
    exact_mod_cast orderFortyNine_sum_neighbor_degrees_center_eq_fifty
      G hfree hmin hcard hHigh hv hvs
  change (D * D) s y = (M * M) s y - 38 - 12 * M s y
  rw [hexpand]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [hBB, hBJ, hJB, hBM, hMB, hJJ, hJM, hMJ]
  ring

/-- Number of leaf-defect neighbors of `y` having the same defect owner
`s`. -/
def orderFortyNineSameOwnerLeafDefectDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s : {z : V // z ∈ G.neighborSet v})
    (y : {z : V // z ≠ v ∧ ¬ G.Adj v z}) : ℕ :=
  ((secondOrderDefectGraph G).neighborFinset y.1 ∩
    orderFortyNineDefectOwnerFiber G v s).card

/-- For an owner--leaf pair, the fourth-walk formula loses its `A²` term:
the same-owner leaf-defect degree is exactly `A⁴(s,y) - 38`. -/
theorem orderFortyNine_sameOwnerLeafDefectDegree_eq_fourthWalk_sub_thirtyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v})
    (y : {z : V // z ≠ v ∧ ¬ G.Adj v z})
    (hy : G.degree y.1 = 7)
    (howner : y.1 ∈ orderFortyNineDefectOwnerFiber G v s) :
    (orderFortyNineSameOwnerLeafDefectDegree G v s y : ℤ) =
      ((G.adjMatrix ℤ * G.adjMatrix ℤ) *
        (G.adjMatrix ℤ * G.adjMatrix ℤ)) s.1 y.1 - 38 := by
  have hvs : G.Adj v s.1 := s.2
  have hDsy : (secondOrderDefectGraph G).Adj s.1 y.1 := by
    exact ((secondOrderDefectGraph G).mem_neighborFinset s.1 y.1).1 howner
  have hsy : s.1 ≠ y.1 := (secondOrderDefectGraph G).ne_of_adj hDsy
  have hA2zero :
      (G.adjMatrix ℤ * G.adjMatrix ℤ) s.1 y.1 = 0 := by
    rw [adjMatrix_sq_apply_eq_card_common]
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hsy).1 hDsy
    rw [hzero]
    simp
  have hformula := orderFortyNine_defectSquare_center_leaf_eq_fourthWalk
    G hfree hmin hcard hHigh hv hvs hy y.2.2
  rw [hA2zero] at hformula
  have hleft :
      (((secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) s.1 y.1) =
        (orderFortyNineSameOwnerLeafDefectDegree G v s y : ℤ) := by
    rw [adjMatrix_sq_apply_eq_card_common]
    congr 1
    rw [orderFortyNineSameOwnerLeafDefectDegree,
      orderFortyNineDefectOwnerFiber, Finset.inter_comm]
  rw [hleft] at hformula
  simpa using hformula

/-- In the one-high stratum the adjacency determinant is divisible by three.
The square-order high-root weight is sent to `-48 e_v`, so its reduction
modulo three is a nonzero kernel vector. -/
theorem orderFortyNine_three_dvd_adjMatrix_det_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    (3 : ℤ) ∣ (G.adjMatrix ℤ).det := by
  have hvHigh : v ∈ orderFortyNineHighVertices G := by
    simp [orderFortyNineHighVertices, hv]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hHigh
  have hvu : v = u := by simpa [hu] using hvHigh
  have hdegree : ∀ {x : V}, x ≠ v → G.degree x = 7 := by
    intro x hx
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard x with hx7 | hx8
    · exact hx7
    · have hxHigh : x ∈ orderFortyNineHighVertices G := by
        simp [orderFortyNineHighVertices, hx8]
      have hxu : x = u := by simpa [hu] using hxHigh
      exact (hx (hxu.trans hvu.symm)).elim
  let w : V → ZMod 3 := fun x =>
    (squareOrderHighRootWeight G 7 v x : ZMod 3)
  have hwne : w ≠ 0 := by
    intro hw
    have hvw := congrFun hw v
    simp [w, squareOrderHighRootWeight] at hvw
  have hker : (G.adjMatrix (ZMod 3)).mulVec w = 0 := by
    funext x
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    change (∑ y ∈ G.neighborFinset x,
      (squareOrderHighRootWeight G 7 v y : ZMod 3)) = 0
    have hsum := sum_squareOrderHighRootWeight_over_neighbors
      G hfree (by omega) hmin (by simpa using hcard) hv hdegree x
    by_cases hxv : x = v
    · subst x
      simp only [if_pos] at hsum
      norm_num at hsum
      have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hsum
      norm_num [Int.cast_sum] at hcast
      exact hcast
    · rw [if_neg hxv] at hsum
      have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hsum
      simp only [Int.cast_zero] at hcast
      simpa using hcast
  have hdet3 : (G.adjMatrix (ZMod 3)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨w, hwne, hker⟩
  have hmap :
      (Int.castRingHom (ZMod 3)).mapMatrix (G.adjMatrix ℤ) =
        G.adjMatrix (ZMod 3) := by
    ext x y
    simp [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  have hdetmap := (Int.castRingHom (ZMod 3)).map_det (G.adjMatrix ℤ)
  rw [hmap, hdet3] at hdetmap
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (G.adjMatrix ℤ).det 3).mp hdetmap

/-- In fact the integral high-root identity gives the much stronger divisor
`48 ∣ det A`.  Multiplying `A w = -48 e_v` by `adjugate A` and reading the
`v` coordinate gives `det(A) = -48 adjugate(A)_{v,v}`, because `w(v)=1`. -/
theorem orderFortyNine_fortyEight_dvd_adjMatrix_det_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    (48 : ℤ) ∣ (G.adjMatrix ℤ).det := by
  have hvHigh : v ∈ orderFortyNineHighVertices G := by
    simp [orderFortyNineHighVertices, hv]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hHigh
  have hvu : v = u := by simpa [hu] using hvHigh
  have hdegree : ∀ {x : V}, x ≠ v → G.degree x = 7 := by
    intro x hx
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard x with hx7 | hx8
    · exact hx7
    · have hxHigh : x ∈ orderFortyNineHighVertices G := by
        simp [orderFortyNineHighVertices, hx8]
      have hxu : x = u := by simpa [hu] using hxHigh
      exact (hx (hxu.trans hvu.symm)).elim
  let A := G.adjMatrix ℤ
  let w := squareOrderHighRootWeight G 7 v
  have hAw : A.mulVec w = fun x => if x = v then (-48 : ℤ) else 0 := by
    simpa [A, w] using
      (adjMatrix_mulVec_squareOrderHighRootWeight
        G hfree (by omega) hmin (by simpa using hcard) hv hdegree)
  have hwv : w v = 1 := by
    simp [w, squareOrderHighRootWeight]
  have hadj := congrArg
    (fun z : V → ℤ => (A.adjugate.mulVec z) v) hAw
  have hleft : (A.adjugate.mulVec (A.mulVec w)) v = A.det := by
    calc
      _ = ((A.adjugate * A).mulVec w) v := by
        rw [Matrix.mulVec_mulVec]
      _ = A.det := by rw [Matrix.adjugate_mul]; simp [hwv]
  have hright :
      (A.adjugate.mulVec (fun x => if x = v then (-48 : ℤ) else 0)) v =
        A.adjugate v v * (-48) := by
    simp [Matrix.mulVec, dotProduct]
  rw [hleft, hright] at hadj
  refine ⟨-A.adjugate v v, ?_⟩
  change A.det = 48 * (-A.adjugate v v)
  rw [hadj]
  ring

/-- The one-high square candidate has determinant divisible by `48² = 2304`.
This retains the full integral content of the high-root kernel identity. -/
theorem orderFortyNine_twoThousandThreeHundredFour_dvd_squareCandidate_det_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    (2304 : ℤ) ∣ (orderFortyNineSquareCandidate G).det := by
  rcases orderFortyNine_fortyEight_dvd_adjMatrix_det_of_one_high
      G hfree hmin hcard hHigh hv with ⟨k, hk⟩
  have hdet : (orderFortyNineSquareCandidate G).det =
      (G.adjMatrix ℤ).det * (G.adjMatrix ℤ).det := by
    rw [← Matrix.det_mul,
      orderFortyNine_adjMatrix_sq_eq_six_add_high_add_ones_sub_defect
        G hfree hmin hcard]
    rfl
  refine ⟨k * k, ?_⟩
  rw [hdet, hk]
  ring

/-- Exact determinant shape in the one-high stratum: the square candidate
has determinant `2304 * k²`.  This is the directly executable rejection
criterion for a finite defect-graph census. -/
theorem orderFortyNine_squareCandidate_det_eq_2304_mul_sq_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ k : ℤ, (orderFortyNineSquareCandidate G).det = 2304 * k ^ 2 := by
  rcases orderFortyNine_fortyEight_dvd_adjMatrix_det_of_one_high
      G hfree hmin hcard hHigh hv with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hdet : (orderFortyNineSquareCandidate G).det =
      (G.adjMatrix ℤ).det * (G.adjMatrix ℤ).det := by
    rw [← Matrix.det_mul,
      orderFortyNine_adjMatrix_sq_eq_six_add_high_add_ones_sub_defect
        G hfree hmin hcard]
    rfl
  rw [hdet, hk]
  ring

/-- In the one-high stratum the square-candidate determinant is divisible by
thirty-six.  Odd order forces `2 ∣ det A`, while the high-root kernel forces
`3 ∣ det A`; the candidate is `A²`. -/
theorem orderFortyNine_thirtySix_dvd_squareCandidate_det_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    (36 : ℤ) ∣ (orderFortyNineSquareCandidate G).det := by
  have hodd : Odd (Fintype.card V) := by rw [hcard]; decide
  have htwo : (2 : ℤ) ∣ (G.adjMatrix ℤ).det :=
    (even_det_adjMatrix_of_odd_card G hodd).two_dvd
  have hthree : (3 : ℤ) ∣ (G.adjMatrix ℤ).det :=
    orderFortyNine_three_dvd_adjMatrix_det_of_one_high
      G hfree hmin hcard hHigh hv
  have hsix : (6 : ℤ) ∣ (G.adjMatrix ℤ).det := by
    have hprod : (2 : ℤ) * 3 ∣ (G.adjMatrix ℤ).det :=
      IsCoprime.mul_dvd (by norm_num) htwo hthree
    norm_num at hprod
    exact hprod
  rcases hsix with ⟨k, hk⟩
  have hdet : (orderFortyNineSquareCandidate G).det =
      (G.adjMatrix ℤ).det * (G.adjMatrix ℤ).det := by
    rw [← Matrix.det_mul,
      orderFortyNine_adjMatrix_sq_eq_six_add_high_add_ones_sub_defect
        G hfree hmin hcard]
    rfl
  refine ⟨k * k, ?_⟩
  rw [hdet, hk]
  ring

/-- The center block of `D²` is `5I`: every defect-owner fiber has size five,
and distinct fibers are disjoint. -/
theorem orderFortyNine_defectSquare_centerBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    ((secondOrderDefectGraph G).adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) s.1 t.1 =
        if s = t then 5 else 0 := by
  let D := secondOrderDefectGraph G
  by_cases hst : s = t
  · subst t
    rw [if_pos rfl, D.adjMatrix_mul_self_apply_self,
      ← D.card_neighborFinset_eq_degree]
    exact_mod_cast orderFortyNine_card_defectOwnerFiber_eq_five_of_one_high
      G hfree hmin hcard hHigh hv s
  · rw [if_neg hst, adjMatrix_sq_apply_eq_card_common]
    have hsAdj : G.Adj v s.1 := s.2
    have htAdj : G.Adj v t.1 := t.2
    have hdisjClosed :=
      orderFortyNine_closedDefectNeighborhood_pairwiseDisjoint_at_high
        G hfree hmin hcard hv
          ((G.mem_neighborFinset v s.1).2 hsAdj)
          ((G.mem_neighborFinset v t.1).2 htAdj)
          (fun h => hst (Subtype.ext h))
    have hinter : D.neighborFinset s.1 ∩ D.neighborFinset t.1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact Finset.disjoint_left.mp hdisjClosed
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mp hy).1))
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mp hy).2))
    rw [hinter]
    simp

/-- The same directed incidence count restricted to one leaf-defect
component. -/
def orderFortyNineLeafComponentBranchIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  ∑ x : c.supp,
    if x.1.1 ∈ secondLayerBranch G v s then
      ((orderFortyNineLeafDefectGraph G v).neighborFinset x.1).filter
        (fun y => y.1 ∈ secondLayerBranch G v t) |>.card
    else 0

/-- Component incidence written intrinsically in the induced component graph.
This presentation makes undirected symmetry available directly. -/
def orderFortyNineLeafComponentBranchIncidenceInduced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  let H := (orderFortyNineLeafDefectGraph G v).induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun x =>
    x.1.1 ∈ secondLayerBranch G v s
  let T : Finset c.supp := Finset.univ.filter fun y =>
    y.1.1 ∈ secondLayerBranch G v t
  ∑ x ∈ S, (H.neighborFinset x ∩ T).card

/-- Intrinsic component branch incidences are symmetric. -/
theorem orderFortyNineLeafComponentBranchIncidenceInduced_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineLeafComponentBranchIncidenceInduced G v c s t =
      orderFortyNineLeafComponentBranchIncidenceInduced G v c t s := by
  exact sum_card_neighbor_inter_comm
    ((orderFortyNineLeafDefectGraph G v).induce c.supp)
    ((Finset.univ : Finset c.supp).filter fun x =>
      x.1.1 ∈ secondLayerBranch G v s)
    ((Finset.univ : Finset c.supp).filter fun y =>
      y.1.1 ∈ secondLayerBranch G v t)

/-- The ambient-neighbor and induced-component presentations of a component
incidence count agree. -/
theorem orderFortyNineLeafComponentBranchIncidence_eq_induced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineLeafComponentBranchIncidence G v c s t =
      orderFortyNineLeafComponentBranchIncidenceInduced G v c s t := by
  let L := orderFortyNineLeafDefectGraph G v
  let H := L.induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun x =>
    x.1.1 ∈ secondLayerBranch G v s
  let T : Finset c.supp := Finset.univ.filter fun y =>
    y.1.1 ∈ secondLayerBranch G v t
  rw [orderFortyNineLeafComponentBranchIncidence,
    orderFortyNineLeafComponentBranchIncidenceInduced]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · apply Finset.card_bij
      (s := (L.neighborFinset x.1).filter fun y =>
        y.1 ∈ secondLayerBranch G v t)
      (t := H.neighborFinset x ∩ T)
      (fun y hy => ⟨y, neighborSet_subset_connectedComponent_supp L c x
        ((L.mem_neighborFinset x.1 y).1 (Finset.mem_filter.mp hy).1)⟩)
    · intro y hy
      have hadj := (L.mem_neighborFinset x.1 y).1
        (Finset.mem_filter.mp hy).1
      exact Finset.mem_inter.mpr ⟨
        (H.mem_neighborFinset x _).2 hadj,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hy).2⟩⟩
    · intro a _ b _ hab
      exact congrArg (fun z => z.1) hab
    · intro y hy
      refine ⟨y.1, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨
        (L.mem_neighborFinset x.1 y.1).2
          ((H.mem_neighborFinset x y).1 (Finset.mem_inter.mp hy).1),
        (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2⟩
  · simp [S, hx]

/-- Component branch incidences are symmetric because the leaf-defect graph
is undirected. -/
theorem orderFortyNineLeafComponentBranchIncidence_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineLeafComponentBranchIncidence G v c s t =
      orderFortyNineLeafComponentBranchIncidence G v c t s := by
  rw [orderFortyNineLeafComponentBranchIncidence_eq_induced,
    orderFortyNineLeafComponentBranchIncidence_eq_induced]
  exact orderFortyNineLeafComponentBranchIncidenceInduced_comm G v c s t

/-- The eight original branch classes partition every leaf-defect connected
component. -/
theorem orderFortyNine_component_branchClasses_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent) :
    let F := fun s : {z : V // z ∈ G.neighborSet v} =>
      (Finset.univ : Finset c.supp).filter fun y =>
        y.1.1 ∈ secondLayerBranch G v s
    ((Finset.univ : Finset {z : V // z ∈ G.neighborSet v}) : Set _).PairwiseDisjoint F ∧
      (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion F =
        Finset.univ := by
  let F := fun s : {z : V // z ∈ G.neighborSet v} =>
    (Finset.univ : Finset c.supp).filter fun y =>
      y.1.1 ∈ secondLayerBranch G v s
  constructor
  · intro s _ t _ hst
    apply Finset.disjoint_left.mpr
    intro y hys hyt
    exact Finset.disjoint_left.mp
      (secondLayerBranch_pairwiseDisjoint G hfree v
        (Finset.mem_univ s) (Finset.mem_univ t) hst)
      (Finset.mem_filter.mp hys).2 (Finset.mem_filter.mp hyt).2
  · apply Finset.eq_univ_of_forall
    intro y
    rw [Finset.mem_biUnion]
    have hyOutside : y.1.1 ∈ Finset.univ \ insert v (G.neighborFinset v) := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        simp [y.1.2.1, y.1.2.2]⟩
    have hySecond : y.1.1 ∈ secondLayer G v := by
      rw [orderFortyNine_secondLayer_degreeEight_eq_compl_closedNeighborhood
        G hfree hmin hcard hv]
      exact hyOutside
    rw [secondLayer, Finset.mem_biUnion] at hySecond
    obtain ⟨s, _, hys⟩ := hySecond
    exact ⟨s, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hys⟩⟩

/-- Every vertex in branch `s` contributes its five component neighbors to
exactly one target branch, so a component incidence row sums to five times
the component branch census. -/
theorem sum_orderFortyNineLeafComponentBranchIncidence_eq_five_mul_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (∑ t, orderFortyNineLeafComponentBranchIncidence G v c s t) =
      orderFortyNineLeafComponentBranchCensus G v c s * 5 := by
  let H := (orderFortyNineLeafDefectGraph G v).induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun x =>
    x.1.1 ∈ secondLayerBranch G v s
  let F := fun t : {z : V // z ∈ G.neighborSet v} =>
    (Finset.univ : Finset c.supp).filter fun y =>
      y.1.1 ∈ secondLayerBranch G v t
  have hpart := orderFortyNine_component_branchClasses_partition
    G hfree hmin hcard hv c
  have hdeg : ∀ x : c.supp, H.degree x = 5 := by
    intro x
    rw [show H.degree x = (orderFortyNineLeafDefectGraph G v).degree x.1 by
      exact degree_induce_connectedComponent_supp
        (orderFortyNineLeafDefectGraph G v) c x]
    exact orderFortyNine_leafDefectGraph_degree_eq_five_of_one_high
      G hfree hmin hcard hHigh hv x.1
  simp_rw [orderFortyNineLeafComponentBranchIncidence_eq_induced]
  change (∑ t, ∑ x ∈ S, (H.neighborFinset x ∩ F t).card) = _
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ S, ∑ t, (H.neighborFinset x ∩ F t).card) =
        ∑ _x ∈ S, 5 := by
      apply Finset.sum_congr rfl
      intro x _
      have hpair : ((Finset.univ : Finset {z : V // z ∈ G.neighborSet v}) :
          Set _).PairwiseDisjoint (fun t => H.neighborFinset x ∩ F t) := by
        intro t _ u _ htu
        apply Finset.disjoint_left.mpr
        intro y hyt hyu
        exact Finset.disjoint_left.mp
          (hpart.1 (Finset.mem_univ t) (Finset.mem_univ u) htu)
          (Finset.mem_inter.mp hyt).2 (Finset.mem_inter.mp hyu).2
      rw [← Finset.card_biUnion hpair]
      have hunion :
          (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion
              (fun t => H.neighborFinset x ∩ F t) = H.neighborFinset x := by
        ext y
        simp only [Finset.mem_biUnion, Finset.mem_inter, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨t, hy, _⟩
          exact hy
        · intro hy
          have hyU : y ∈
              (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion F := by
            rw [hpart.2]
            exact Finset.mem_univ y
          rw [Finset.mem_biUnion] at hyU
          obtain ⟨t, _, hyt⟩ := hyU
          exact ⟨t, hy, hyt⟩
      rw [hunion, H.card_neighborFinset_eq_degree, hdeg]
    _ = orderFortyNineLeafComponentBranchCensus G v c s * 5 := by
      simp [S, orderFortyNineLeafComponentBranchCensus]

/-- Original branch classes are independent in the leaf-defect graph, hence
every diagonal component incidence vanishes. -/
theorem orderFortyNineLeafComponentBranchIncidence_self_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineLeafComponentBranchIncidence G v c s s = 0 := by
  rw [orderFortyNineLeafComponentBranchIncidence_eq_induced]
  let H := (orderFortyNineLeafDefectGraph G v).induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun x =>
    x.1.1 ∈ secondLayerBranch G v s
  change (∑ x ∈ S, (H.neighborFinset x ∩ S).card) = 0
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hxBranch := (Finset.mem_filter.mp hx).2
  have hyBranch := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  exact orderFortyNineLeafDefect_not_adj_of_same_originalBranch
    G hfree s x.1 y.1 hxBranch hyBranch
      ((H.mem_neighborFinset x y).1 (Finset.mem_inter.mp hy).1)

/-- A component cross-branch incidence count is bounded by the product of
the two component branch populations. -/
theorem orderFortyNineLeafComponentBranchIncidence_le_census_mul_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineLeafComponentBranchIncidence G v c s t ≤
      orderFortyNineLeafComponentBranchCensus G v c s *
        orderFortyNineLeafComponentBranchCensus G v c t := by
  rw [orderFortyNineLeafComponentBranchIncidence_eq_induced]
  let H := (orderFortyNineLeafDefectGraph G v).induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun x =>
    x.1.1 ∈ secondLayerBranch G v s
  let T : Finset c.supp := Finset.univ.filter fun y =>
    y.1.1 ∈ secondLayerBranch G v t
  change (∑ x ∈ S, (H.neighborFinset x ∩ T).card) ≤ _
  calc
    (∑ x ∈ S, (H.neighborFinset x ∩ T).card) ≤
        ∑ _x ∈ S, T.card := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.card_le_card Finset.inter_subset_right
    _ = orderFortyNineLeafComponentBranchCensus G v c s *
          orderFortyNineLeafComponentBranchCensus G v c t := by
      simp [S, T, orderFortyNineLeafComponentBranchCensus]

/-- In an order-six component the induced leaf-defect graph is `K₆`, so every
two distinct branch classes span all possible edges. -/
theorem orderFortyNineLeafComponentBranchIncidence_eq_census_mul_census_of_order_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent)
    (hc : Fintype.card c.supp = 6)
    (s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t) :
    orderFortyNineLeafComponentBranchIncidence G v c s t =
      orderFortyNineLeafComponentBranchCensus G v c s *
        orderFortyNineLeafComponentBranchCensus G v c t := by
  rw [orderFortyNineLeafComponentBranchIncidence_eq_induced]
  let L := orderFortyNineLeafDefectGraph G v
  let H := L.induce c.supp
  let S : Finset c.supp := Finset.univ.filter fun x =>
    x.1.1 ∈ secondLayerBranch G v s
  let T : Finset c.supp := Finset.univ.filter fun y =>
    y.1.1 ∈ secondLayerBranch G v t
  have hHreg : ∀ x : c.supp, H.degree x = 5 := by
    intro x
    rw [show H.degree x = L.degree x.1 by
      exact degree_induce_connectedComponent_supp L c x]
    exact orderFortyNine_leafDefectGraph_degree_eq_five_of_one_high
      G hfree hmin hcard hHigh hv x.1
  have hneighbors : ∀ x : c.supp,
      H.neighborFinset x = Finset.univ.erase x := by
    intro x
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      exact Finset.mem_erase.mpr ⟨
        (H.ne_of_adj ((H.mem_neighborFinset x y).1 hy)).symm,
        Finset.mem_univ _⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ x),
        Finset.card_univ, hc, H.card_neighborFinset_eq_degree, hHreg]
  change (∑ x ∈ S, (H.neighborFinset x ∩ T).card) = _
  have hinter : ∀ x ∈ S, H.neighborFinset x ∩ T = T := by
    intro x hx
    rw [hneighbors]
    apply Finset.inter_eq_right.mpr
    intro y hy
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hyx
    subst y
    exact Finset.disjoint_left.mp
      (secondLayerBranch_pairwiseDisjoint G hfree v
        (Finset.mem_univ s) (Finset.mem_univ t) hst)
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  calc
    (∑ x ∈ S, (H.neighborFinset x ∩ T).card) =
        ∑ _x ∈ S, T.card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hinter x hx]
    _ = orderFortyNineLeafComponentBranchCensus G v c s *
          orderFortyNineLeafComponentBranchCensus G v c t := by
      simp [S, T, orderFortyNineLeafComponentBranchCensus]

/-- Directed cross-branch incidences decompose exactly over connected
components. -/
theorem sum_orderFortyNineLeafComponentBranchIncidence_eq_global
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
      orderFortyNineLeafComponentBranchIncidence G v c s t) =
        orderFortyNineLeafDefectBranchIncidence G v s t := by
  let f := fun x : {z : V // z ≠ v ∧ ¬ G.Adj v z} =>
    if x.1 ∈ secondLayerBranch G v s then
      ((orderFortyNineLeafDefectGraph G v).neighborFinset x).filter
        (fun y => y.1 ∈ secondLayerBranch G v t) |>.card
    else 0
  change (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
    ∑ x : c.supp, f x.1) = ∑ x, f x
  exact (sum_vertex_eq_sum_connectedComponent_supp
    (orderFortyNineLeafDefectGraph G v) f).symm

/-- The finset block and degree-sum presentations of directed cross-branch
leaf-defect edges agree. -/
theorem card_orderFortyNineLeafDefectBranchBlock_eq_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    (orderFortyNineLeafDefectBranchBlock G v s t).card =
      orderFortyNineLeafDefectBranchIncidence G v s t := by
  let W := {z : V // z ≠ v ∧ ¬ G.Adj v z}
  let A : Finset W := Finset.univ.filter fun x =>
    x.1 ∈ secondLayerBranch G v s
  let B : W → Finset W := fun x =>
    ((orderFortyNineLeafDefectGraph G v).neighborFinset x).filter fun y =>
      y.1 ∈ secondLayerBranch G v t
  have hIncidence : orderFortyNineLeafDefectBranchIncidence G v s t =
      (A.sigma B).card := by
    rw [orderFortyNineLeafDefectBranchIncidence, Finset.card_sigma]
    rw [Finset.sum_filter]
  rw [hIncidence]
  apply Finset.card_bij
    (s := orderFortyNineLeafDefectBranchBlock G v s t) (t := A.sigma B)
    (fun xy hxy =>
    let hx := (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).1
    let hy := (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).2
    let x' : W := ⟨xy.1, by
      have hout := (Finset.mem_sdiff.mp hx).2
      exact ⟨fun h => hout (by simp [h]), fun hvx => hout (by
        simp [SimpleGraph.mem_neighborFinset, hvx])⟩⟩
    let y' : W := ⟨xy.2, by
      have hout := (Finset.mem_sdiff.mp hy).2
      exact ⟨fun h => hout (by simp [h]), fun hvy => hout (by
        simp [SimpleGraph.mem_neighborFinset, hvy])⟩⟩
    ⟨x', y'⟩)
  · intro xy hxy
    have hmem := Finset.mem_filter.mp hxy
    have hprod := Finset.mem_product.mp hmem.1
    rw [Finset.mem_sigma]
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprod.1⟩
    · exact Finset.mem_filter.mpr ⟨
        ((orderFortyNineLeafDefectGraph G v).mem_neighborFinset _ _).2 hmem.2,
        hprod.2⟩
  · intro a ha b hb hab
    exact Prod.ext (congrArg (fun z => z.1.1) hab)
      (congrArg (fun z => z.2.1) hab)
  · intro xy hxy
    have hxA := (Finset.mem_sigma.mp hxy).1
    have hyB := (Finset.mem_sigma.mp hxy).2
    have hx := (Finset.mem_filter.mp hxA).2
    have hy := (Finset.mem_filter.mp hyB).2
    refine ⟨(xy.1.1, xy.2.1), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩,
      ((orderFortyNineLeafDefectGraph G v).mem_neighborFinset xy.1 xy.2).1
        (Finset.mem_filter.mp hyB).1⟩

/-- Cross-branch leaf-defect edge blocks are the sum of their componentwise
incidence counts. -/
theorem card_orderFortyNineLeafDefectBranchBlock_eq_sum_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    (orderFortyNineLeafDefectBranchBlock G v s t).card =
      ∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
        orderFortyNineLeafComponentBranchIncidence G v c s t := by
  rw [card_orderFortyNineLeafDefectBranchBlock_eq_incidence,
    sum_orderFortyNineLeafComponentBranchIncidence_eq_global]

/-- Exact mate rigidity with every cross-branch leaf-defect edge count
decomposed into its connected-component contributions. -/
theorem exists_orderFortyNine_mate_exact_componentLeafDefect_overlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ mate : {z : V // z ∈ G.neighborSet v} →
        {z : V // z ∈ G.neighborSet v},
      Function.Involutive mate ∧
      (∀ s, G.Adj s.1 (mate s).1) ∧
      ∀ s,
        ((∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
            orderFortyNineLeafComponentBranchIncidence G v c s (mate s)) +
          orderFortyNineOneHighOverlap G v s s +
          orderFortyNineOneHighOverlap G v (mate s) (mate s) = 5) ∧
        ∀ u ∈ ((Finset.univ.erase s).erase (mate s)),
          (∑ c : (orderFortyNineLeafDefectGraph G v).ConnectedComponent,
              orderFortyNineLeafComponentBranchIncidence G v c s u) +
            orderFortyNineOneHighOverlap G v s (mate u) +
            orderFortyNineOneHighOverlap G v u (mate s) = 5 := by
  obtain ⟨mate, hmateInv, hmateAdj, hrigid⟩ :=
    exists_orderFortyNine_mate_exact_leafDefect_overlap
      G hfree hmin hcard hHigh hv
  refine ⟨mate, hmateInv, hmateAdj, ?_⟩
  intro s
  constructor
  · rw [← card_orderFortyNineLeafDefectBranchBlock_eq_sum_components]
    exact (hrigid s).1
  · intro u hu
    rw [← card_orderFortyNineLeafDefectBranchBlock_eq_sum_components]
    exact (hrigid s).2 u hu

end

end Erdos85
