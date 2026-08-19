import Proofs.Erdos85SizeTwoMuNegFiveInternalNeutralDichotomy

/-! # Exact rooted triangle census at `mu=-5` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The internal/neutral overlap and total rooted triangle count have exactly
two profiles on both shores: equality type `(2,4)` and disjoint type `(0,3)`.
Here the second coordinate counts edges in the induced neighborhood, hence
triangles rooted at the shore vertex. -/
theorem orderSixtyFour_sizeTwo_muNegFive_triangle_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
    let N := MuNegFiveNeutralProjection G c s
    (∀ x : Xp,
      ((triangleFreeEdgeGraph G).degree x.1 = 0 ∧
        ((Finset.univ : Finset Xm).filter fun y => B x y ∧ N x y).card = 2 ∧
        (G.induce (G.neighborSet x.1)).edgeFinset.card = 4) ∨
      ((triangleFreeEdgeGraph G).degree x.1 = 2 ∧
        ((Finset.univ : Finset Xm).filter fun y => B x y ∧ N x y).card = 0 ∧
        (G.induce (G.neighborSet x.1)).edgeFinset.card = 3)) ∧
    ∀ y : Xm,
      ((triangleFreeEdgeGraph G).degree y.1 = 0 ∧
        ((Finset.univ : Finset Xp).filter fun x => B x y ∧ N x y).card = 2 ∧
        (G.induce (G.neighborSet y.1)).edgeFinset.card = 4) ∨
      ((triangleFreeEdgeGraph G).degree y.1 = 2 ∧
        ((Finset.univ : Finset Xp).filter fun x => B x y ∧ N x y).card = 0 ∧
        (G.induce (G.neighborSet y.1)).edgeFinset.card = 3) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
  let N := MuNegFiveNeutralProjection G c s
  have hrow := orderSixtyFour_sizeTwo_muNegFive_internal_neutral_row_dichotomy
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcol := orderSixtyFour_sizeTwo_muNegFive_internal_neutral_column_dichotomy
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hNregular := orderSixtyFour_sizeTwo_muNegFive_neutralProjection_biregular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  constructor
  · intro x
    rcases hrow x with hzero | htwo
    · left
      refine ⟨hzero.1, ?_, ?_⟩
      · have heq : ((Finset.univ : Finset Xm).filter fun y =>
            B x y ∧ N x y) =
            ((Finset.univ : Finset Xm).filter fun y => N x y) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact and_iff_right_of_imp fun hN => (hzero.2 y).2 hN
        rw [heq, hNregular.1 x]
      · have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x.1
        have htfcard : (triangleFreeNeighbors G x.1).card = 0 := by
          calc
            _ = (triangleFreeEdgeGraph G).degree x.1 := by
              rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
                triangleFreeEdgeGraph_neighborFinset]
            _ = 0 := hzero.1
        rw [htfcard, hreg x.1] at hid
        omega
    · right
      refine ⟨htwo.1, ?_, ?_⟩
      · apply Finset.card_eq_zero.mpr
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨y, hy⟩
        have hd := (Finset.mem_filter.mp hy).2
        exact (htwo.2 y hd.1) hd.2
      · have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x.1
        have htfcard : (triangleFreeNeighbors G x.1).card = 2 := by
          calc
            _ = (triangleFreeEdgeGraph G).degree x.1 := by
              rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
                triangleFreeEdgeGraph_neighborFinset]
            _ = 2 := htwo.1
        rw [htfcard, hreg x.1] at hid
        omega
  · intro y
    rcases hcol y with hzero | htwo
    · left
      refine ⟨hzero.1, ?_, ?_⟩
      · have heq : ((Finset.univ : Finset Xp).filter fun x =>
            B x y ∧ N x y) =
            ((Finset.univ : Finset Xp).filter fun x => N x y) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact and_iff_right_of_imp fun hN => (hzero.2 x).2 hN
        rw [heq, hNregular.2 y]
      · have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree y.1
        have htfcard : (triangleFreeNeighbors G y.1).card = 0 := by
          calc
            _ = (triangleFreeEdgeGraph G).degree y.1 := by
              rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
                triangleFreeEdgeGraph_neighborFinset]
            _ = 0 := hzero.1
        rw [htfcard, hreg y.1] at hid
        omega
    · right
      refine ⟨htwo.1, ?_, ?_⟩
      · apply Finset.card_eq_zero.mpr
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨x, hx⟩
        have hd := (Finset.mem_filter.mp hx).2
        exact (htwo.2 x hd.1) hd.2
      · have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree y.1
        have htfcard : (triangleFreeNeighbors G y.1).card = 2 := by
          calc
            _ = (triangleFreeEdgeGraph G).degree y.1 := by
              rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
                triangleFreeEdgeGraph_neighborFinset]
            _ = 2 := htwo.1
        rw [htfcard, hreg y.1] at hid
        omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_triangle_census
