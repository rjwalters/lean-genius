import Proofs.Erdos85BinarySquareSizeTwoCrossBipartiteComponentBound

/-! # Side balance inside every cross-block cycle -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Vertices on the source side of one connected cross-block component. -/
def crossComponentLeftVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (e : (componentCrossBipartiteGraph G c d).ConnectedComponent) :
    Finset e.supp := by
  classical
  exact Finset.univ.filter fun v => match v.1 with
      | Sum.inl _ => True
      | Sum.inr _ => False

/-- Vertices on the target side of one connected cross-block component. -/
def crossComponentRightVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (e : (componentCrossBipartiteGraph G c d).ConnectedComponent) :
    Finset e.supp := by
  classical
  exact Finset.univ.filter fun v => match v.1 with
      | Sum.inl _ => False
      | Sum.inr _ => True

/-- Every connected component of a component cross block contains equally
many source-side and target-side vertices.  This is a degree-sum double count
inside the induced connected component. -/
theorem componentCrossBipartiteComponent_left_card_eq_right_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hdeg : ∀ v, (componentCrossBipartiteGraph G c d).degree v = 2)
    (e : (componentCrossBipartiteGraph G c d).ConnectedComponent) :
    (crossComponentLeftVertices G c d e).card =
      (crossComponentRightVertices G c d e).card := by
  let H := componentCrossBipartiteGraph G c d
  let K := H.induce e.supp
  letI : DecidableRel K.Adj := Classical.decRel _
  letI : K.LocallyFinite := fun _ => inferInstance
  let L := crossComponentLeftVertices G c d e
  let R := crossComponentRightVertices G c d e
  have hKdeg : ∀ v, K.degree v = 2 := by
    intro v
    change (H.induce e.supp).degree v = 2
    have hsubset : H.neighborSet v.1 ⊆ e.supp := by
      intro w hw
      exact (ConnectedComponent.mem_supp_congr_adj e hw).mp v.2
    exact (SimpleGraph.degree_induce_of_neighborSet_subset
      (G := H) (s := e.supp) hsubset).trans (hdeg v.1)
  have hbip : K.IsBipartiteWith L R := by
    constructor
    · rw [Set.disjoint_left]
      intro v hvL hvR
      rcases v with ⟨v, hv⟩
      cases v <;> simp [L, R, crossComponentLeftVertices,
        crossComponentRightVertices] at hvL hvR
    · intro u v huv
      rcases u with ⟨u, hu⟩
      rcases v with ⟨v, hv⟩
      cases u with
      | inl x =>
        cases v with
        | inl y => simp [K, H, componentCrossBipartiteGraph] at huv
        | inr y =>
          left
          simp [L, R, crossComponentLeftVertices,
            crossComponentRightVertices]
      | inr x =>
        cases v with
        | inl y =>
          right
          simp [L, R, crossComponentLeftVertices,
            crossComponentRightVertices]
        | inr y => simp [K, H, componentCrossBipartiteGraph] at huv
  have hsum := isBipartiteWith_sum_degrees_eq hbip
  simp_rw [hKdeg] at hsum
  simp [Finset.sum_const] at hsum
  simpa [L, R] using hsum

/-- In the binary-square size-two setting, every cross-block cycle has equal
halves in the two defect components. -/
theorem binarySquare_regular_twoSizeTwoParts_crossComponent_side_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (e : (componentCrossBipartiteGraph G c d).ConnectedComponent) :
    (crossComponentLeftVertices G c d e).card =
      (crossComponentRightVertices G c d e).card :=
  componentCrossBipartiteComponent_left_card_eq_right_card G c d
    (binarySquare_regular_twoSizeTwoParts_crossBipartiteGraph_degree_two
      G hfree hq hreg hcard c d hc hd) e

end

end Erdos85
