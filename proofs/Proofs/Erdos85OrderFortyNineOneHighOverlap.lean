import Proofs.Erdos85OrderFortyNineHighBranchGeometry
import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85LocalTriangleParity
import Proofs.Erdos85OrderFortyNineDistOnePinning
import Proofs.Erdos85BranchDeficitSymmetry
import Proofs.Erdos85PairedBlockRigidity
import Proofs.Erdos85MinimumSectorAssemblyInterface

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

end

end Erdos85
