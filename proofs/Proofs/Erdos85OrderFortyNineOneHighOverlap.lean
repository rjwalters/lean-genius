import Proofs.Erdos85OrderFortyNineHighBranchGeometry
import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85LocalTriangleParity
import Proofs.Erdos85OrderFortyNineDistOnePinning
import Proofs.Erdos85BranchDeficitSymmetry

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

end

end Erdos85
