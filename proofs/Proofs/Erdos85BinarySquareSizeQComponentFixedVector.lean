import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85DefectTwinPoleFixedVector

/-!
# Fixed vectors from an order-q defect component

An order-`q` component of the `(q-1)`-regular second-order defect graph is a
clique and has no defect edges leaving it.  Hence every two distinct vertices
in it are adjacent twins.  Their pair indicator is therefore fixed over F₂.
-/

open SimpleGraph

namespace Erdos85

/-- Distinct vertices in an order-`q` binary-square defect component are
adjacent and have identical defect adjacency away from each other. -/
theorem binarySquare_regular_sizeQ_defectComponent_adjacent_twins
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q)
    (pole₁ pole₂ : V)
    (hpole₁ : (secondOrderDefectGraph G).connectedComponentMk pole₁ = c)
    (hpole₂ : (secondOrderDefectGraph G).connectedComponentMk pole₂ = c)
    (hpoles : pole₁ ≠ pole₂) :
    (secondOrderDefectGraph G).Adj pole₁ pole₂ ∧
      ∀ v, v ≠ pole₁ → v ≠ pole₂ →
        ((secondOrderDefectGraph G).Adj v pole₁ ↔
          (secondOrderDefectGraph G).Adj v pole₂) := by
  let D := secondOrderDefectGraph G
  have hadj : D.Adj pole₁ pole₂ :=
    binarySquare_regular_sizeQ_defectComponent_adj
      G hfree hq hreg hcard c hc hpole₁ hpole₂ hpoles
  refine ⟨hadj, ?_⟩
  intro v hv₁ hv₂
  constructor
  · intro hvAdj
    have hvComp : D.connectedComponentMk v = c :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvAdj).trans hpole₁
    exact binarySquare_regular_sizeQ_defectComponent_adj
      G hfree hq hreg hcard c hc hvComp hpole₂ hv₂
  · intro hvAdj
    have hvComp : D.connectedComponentMk v = c :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvAdj).trans hpole₂
    exact binarySquare_regular_sizeQ_defectComponent_adj
      G hfree hq hreg hcard c hc hvComp hpole₁ hv₁

/-- Any distinct pair in an order-`q` second-order-defect component gives a
binary fixed vector, independently of any full/empty-center presentation. -/
theorem binarySquare_adjMatrix_mulVec_twoCoordinate_eq_self_of_sizeQ_defectComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q)
    (pole₁ pole₂ : V)
    (hpole₁ : (secondOrderDefectGraph G).connectedComponentMk pole₁ = c)
    (hpole₂ : (secondOrderDefectGraph G).connectedComponentMk pole₂ = c)
    (hpoles : pole₁ ≠ pole₂) :
    ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  have htwins := binarySquare_regular_sizeQ_defectComponent_adjacent_twins
    G hfree hq hreg hcard c hc pole₁ pole₂ hpole₁ hpole₂ hpoles
  exact secondOrderDefect_mulVec_twoCoordinate_eq_self_of_adjacent_twins
    G pole₁ pole₂ hpoles htwins.1 htwins.2

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeQ_defectComponent_adjacent_twins
#print axioms Erdos85.binarySquare_adjMatrix_mulVec_twoCoordinate_eq_self_of_sizeQ_defectComponent
