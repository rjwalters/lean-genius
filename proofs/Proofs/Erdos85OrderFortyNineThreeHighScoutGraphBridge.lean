import Proofs.Erdos85OrderFortyNineThreeHighGeometrySemantics
import Proofs.Erdos85OrderFortyNineSmallHighLabelingBridge

/-! # Graph-facing bridge for the normalized three-high scouts -/

namespace Erdos85

open SimpleGraph

def OrderFortyNineGraphPinnedMatchingRealized
    (G : SimpleGraph (Fin 49))
    (vertices : List (Fin 49))
    (matching : List (Fin 49 × Fin 49)) : Prop :=
  ∀ ab ∈ orderFortyNineStrictPairs vertices,
    (G.Adj ab.1 ab.2 ↔ ab ∈ matching)

theorem orderFortyNineGraphPinnedMatchingRealized_edges
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    {vertices : List (Fin 49)} {matching : List (Fin 49 × Fin 49)}
    (hrealized : OrderFortyNineGraphPinnedMatchingRealized
      G vertices matching) :
    OrderFortyNinePinnedMatchingRealized
      (orderFortyNineGraphEdges G) vertices matching := by
  intro ab hab
  rw [orderFortyNineBitAdj_graphEdges]
  exact Bool.decide_congr (hrealized ab hab)

def OrderFortyNineThreeHighDistTwoRootEmptyGraphRealized
    (G : SimpleGraph (Fin 49)) : Prop :=
  ∀ z ∈ orderFortyNineThreeHighDistTwoRootEmptyVertices,
    (G.Adj 3 z ↔ z = 13)

theorem orderFortyNineThreeHighDistTwoRootEmptyGraphRealized_edges
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hrealized : OrderFortyNineThreeHighDistTwoRootEmptyGraphRealized G) :
    OrderFortyNineThreeHighDistTwoRootEmptyRealized
      (orderFortyNineGraphEdges G) := by
  intro z hz
  rw [orderFortyNineBitAdj_graphEdges]
  exact Bool.decide_congr (hrealized z hz)

def ThreeHighDistTwoScoutAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49)) : Prop :=
  let H := orderFortyNineRelabeledGraph G E
  SmallHighAlignedLabeling 3 G E orderFortyNineThreeHighDistTwoMasks ∧
  OrderFortyNineGraphPinnedMatchingRealized H
    [3, 4, 5, 6, 7, 8, 9, 10] [(3, 4), (5, 6), (7, 8), (9, 10)] ∧
  OrderFortyNineGraphPinnedMatchingRealized H
    [3, 11, 14, 15, 16, 17, 18, 19]
    [(3, 11), (14, 15), (16, 17), (18, 19)] ∧
  OrderFortyNineGraphPinnedMatchingRealized H
    [3, 12, 20, 21, 22, 23, 24, 25]
    [(3, 12), (20, 21), (22, 23), (24, 25)] ∧
  OrderFortyNineThreeHighDistTwoRootEmptyGraphRealized H

def ThreeHighDistOneC2ScoutAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49)) : Prop :=
  let H := orderFortyNineRelabeledGraph G E
  SmallHighAlignedLabeling 3 G E orderFortyNineThreeHighDistOneC2Masks ∧
  OrderFortyNineGraphPinnedMatchingRealized H
    [3, 4, 5, 6, 7, 8, 9, 10] [(3, 4), (5, 6), (7, 8), (9, 10)] ∧
  OrderFortyNineGraphPinnedMatchingRealized H
    [3, 12, 13, 14, 15, 16, 17, 25]
    [(3, 25), (12, 13), (14, 15), (16, 17)] ∧
  OrderFortyNineGraphPinnedMatchingRealized H
    [5, 18, 19, 20, 21, 22, 23, 25]
    [(5, 18), (19, 25), (20, 21), (22, 23)]

theorem false_of_threeHighDistTwoScoutAlignedLabeling_lrat
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistTwoScoutAlignedLabeling G E)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      orderFortyNineGeneratedThreeHighDistTwoScoutCnf) : False := by
  rcases haligned with ⟨hlabel, h0, h1, h2, hroot⟩
  let H := orderFortyNineRelabeledGraph G E
  let edges := orderFortyNineGraphEdges H
  apply false_of_orderFortyNine_generated_h3_distTwo_scout_lrat
    (edges := edges)
    (orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
      (h := 3) (by omega) G hfree E orderFortyNineThreeHighDistTwoMasks hlabel)
    (orderFortyNineThreeHighDistTwoGeometryClauses_satisfied
      (orderFortyNineGraphPinnedMatchingRealized_edges H h0)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h1)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h2)
      (orderFortyNineThreeHighDistTwoRootEmptyGraphRealized_edges H hroot))
    proof hcheck

theorem false_of_threeHighDistOneC2ScoutAlignedLabeling_lrat
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneC2ScoutAlignedLabeling G E)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf) : False := by
  rcases haligned with ⟨hlabel, h0, h1, h2⟩
  let H := orderFortyNineRelabeledGraph G E
  let edges := orderFortyNineGraphEdges H
  apply false_of_orderFortyNine_generated_h3_distOneC2_scout_lrat
    (edges := edges)
    (orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
      (h := 3) (by omega) G hfree E orderFortyNineThreeHighDistOneC2Masks hlabel)
    (orderFortyNineThreeHighDistOneC2GeometryClauses_satisfied
      (orderFortyNineGraphPinnedMatchingRealized_edges H h0)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h1)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h2))
    proof hcheck

end Erdos85
