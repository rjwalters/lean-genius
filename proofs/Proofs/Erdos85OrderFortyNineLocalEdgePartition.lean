import Proofs.Erdos85LocalTriangleParity
import Proofs.Erdos85OrderFortyNineHighPartnerBound

/-!
# Local high--low and low--low edge accounting at order 49

At a degree-seven vertex, every high neighbor lies on a unique local triangle
edge.  These edges are distinct, since two high vertices cannot be adjacent.
Thus the number of high neighbors is at most the number of local triangle
edges.  The residual count is the number of local edges not charged to a high
endpoint, and the triangle-parity identity bounds their sum by three.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The high neighbors of a low vertex inject into the edges of its local
graph, by sending a high neighbor to its unique triangle edge. -/
theorem orderFortyNine_highNeighborCount_le_localTriangleEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7) :
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card ≤
      (G.induce (G.neighborSet x)).edgeFinset.card := by
  classical
  let S : Finset V :=
    G.neighborFinset x ∩ orderFortyNineHighVertices G
  let N := {z : V // z ∈ G.neighborSet x}
  let H : SimpleGraph N := G.induce (G.neighborSet x)
  have hS_high : ∀ v ∈ S, G.degree v = 8 := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  have hS_adj : ∀ v ∈ S, G.Adj v x := by
    intro v hv
    have := (Finset.mem_inter.mp hv).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hpartner_card : ∀ v : {v // v ∈ S},
      (G.neighborFinset v.1 ∩ G.neighborFinset x).card = 1 := by
    intro v
    let xv : {z : V // z ∈ G.neighborSet v.1} :=
      ⟨x, hS_adj v.1 v.2⟩
    have hdeg := orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
      G hfree hmin hcard (hS_high v.1 v.2) xv
    rwa [degree_induce_neighborSet_eq_card_common] at hdeg
  let partner : {v // v ∈ S} → V := fun v =>
    ((Finset.card_pos.mp (by rw [hpartner_card v]; norm_num)).choose)
  have hpartner_mem : ∀ v : {v // v ∈ S},
      partner v ∈ G.neighborFinset v.1 ∩ G.neighborFinset x := by
    intro v
    exact (Finset.card_pos.mp (by rw [hpartner_card v]; norm_num)).choose_spec
  let highLocal : {v // v ∈ S} → N := fun v =>
    ⟨v.1, by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_inter.mp v.2).1⟩
  let partnerLocal : {v // v ∈ S} → N := fun v =>
    ⟨partner v, by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_inter.mp (hpartner_mem v)).2⟩
  let chargedEdge : {v // v ∈ S} → Sym2 N := fun v =>
    s(highLocal v, partnerLocal v)
  have hcharged_mem : ∀ v : {v // v ∈ S},
      chargedEdge v ∈ H.edgeFinset := by
    intro v
    apply H.mem_edgeFinset.mpr
    change G.Adj v.1 (partner v)
    simpa [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp (hpartner_mem v)).1
  have hcharged_injective : Function.Injective chargedEdge := by
    intro v w heq
    have hor := (Sym2.mk_eq_mk_iff
      (p := (highLocal v, partnerLocal v))
      (q := (highLocal w, partnerLocal w))).mp heq
    rcases hor with hsame | hswap
    · apply Subtype.ext
      exact congrArg (fun q : N × N => q.1.1) hsame
    · exfalso
      have hvw : G.Adj v.1 w.1 := by
        have hpv : partner v = w.1 :=
          congrArg (fun q : N × N => q.2.1) hswap
        have hvp := (Finset.mem_inter.mp (hpartner_mem v)).1
        simpa [hpv] using hvp
      exact orderFortyNine_not_adj_degreeEight_degreeEight
        G hfree hmin hcard (hS_high v.1 v.2) (hS_high w.1 w.2) hvw
  have hcard_le : Fintype.card {v // v ∈ S} ≤ Fintype.card H.edgeFinset :=
    Fintype.card_le_of_injective
      (fun v => ⟨chargedEdge v, hcharged_mem v⟩)
      (fun _ _ h => hcharged_injective (congrArg Subtype.val h))
  change S.card ≤ H.edgeFinset.card
  simpa only [Fintype.card_coe] using hcard_le

/-- The residual local-edge count after charging one distinct local edge to
each high neighbor.  The preceding injection shows that this subtraction is
exact (and not truncated). -/
def orderFortyNineLowLowLocalEdgeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℕ :=
  (G.induce (G.neighborSet x)).edgeFinset.card -
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card

/-- Exact local partition: charged high--low edges plus the residual low--low
edge count give all local triangle edges. -/
theorem orderFortyNine_high_add_lowLow_eq_localTriangleEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7) :
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card +
        orderFortyNineLowLowLocalEdgeCount G x =
      (G.induce (G.neighborSet x)).edgeFinset.card := by
  unfold orderFortyNineLowLowLocalEdgeCount
  exact Nat.add_sub_of_le (orderFortyNine_highNeighborCount_le_localTriangleEdges
    G hfree hmin hcard hx)

/-- The desired local budget: high neighbors and residual low--low local
triangle edges together consume at most three matching edges. -/
theorem orderFortyNine_high_add_lowLow_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7) :
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card +
      orderFortyNineLowLowLocalEdgeCount G x ≤ 3 := by
  rw [orderFortyNine_high_add_lowLow_eq_localTriangleEdges
    G hfree hmin hcard hx]
  exact (localTriangleEdges_le_three_of_degree_seven G hfree hx).1

/-- Equivalent residual form of the local budget. -/
theorem orderFortyNine_lowLowLocalEdgeCount_le_three_sub_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7) :
    orderFortyNineLowLowLocalEdgeCount G x ≤
      3 - (G.neighborFinset x ∩ orderFortyNineHighVertices G).card := by
  have hbudget := orderFortyNine_high_add_lowLow_le_three
    G hfree hmin hcard hx
  omega

/-- A low vertex incident with three high vertices has no residual all-low
local triangle edge. -/
theorem orderFortyNine_lowLowLocalEdgeCount_eq_zero_of_three_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7)
    (hk : (G.neighborFinset x ∩
      orderFortyNineHighVertices G).card = 3) :
    orderFortyNineLowLowLocalEdgeCount G x = 0 := by
  have hbudget := orderFortyNine_high_add_lowLow_le_three
    G hfree hmin hcard hx
  omega

/-- A low vertex with no high neighbor has a positive residual local edge,
recovering the forced all-low triangle numerically. -/
theorem orderFortyNine_lowLowLocalEdgeCount_pos_of_no_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7)
    (hk : (G.neighborFinset x ∩
      orderFortyNineHighVertices G).card = 0) :
    0 < orderFortyNineLowLowLocalEdgeCount G x := by
  rcases orderFortyNine_exists_allLow_triangle_of_highNeighborCount_zero
    G hfree hmin hcard hx hk with ⟨y, z, _hy, _hz, hxy, hxz, hyz⟩
  have hedge : 0 < (G.induce (G.neighborSet x)).edgeFinset.card := by
    rw [Finset.card_pos]
    refine ⟨s(⟨y, hxy⟩, ⟨z, hxz⟩), ?_⟩
    exact (G.induce (G.neighborSet x)).mem_edgeFinset.mpr hyz
  unfold orderFortyNineLowLowLocalEdgeCount
  rw [hk, Nat.sub_zero]
  exact hedge

end

end Erdos85
