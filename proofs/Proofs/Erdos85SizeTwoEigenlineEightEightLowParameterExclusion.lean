import Proofs.Erdos85SizeTwoEigenlineEightEightLowParameterDiagonalModels

/-!
# Excluding the low `8+8` quotient parameters

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

At cross parameter three or two, the diagonal quotient is respectively four
or five.  The exact diagonal models force the offset-two pair.  Its two
endpoints share the intervening ambient-cycle vertex, so they cannot form a
second-order defect edge.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Diagonal quotient four or five is impossible on an all-triangle-free C8
shore: both exact models contain the forbidden offset-two defect edge. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_lowParameter_false
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp)
    (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (d : ℕ) (hd : d = 4 ∨ d = 5)
    (hdiagQ : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = d) :
    False := by
  have hoff :=
    binarySquare_regular_sizeTwoPart_eight_allTriangleFree_low_diagonal_defectAdj_iff
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a u huinj
        hurange hu htf d hd hdiagQ
  have hDsub : ((secondOrderDefectGraph G).induce c.supp).Adj (u 0) (u 2) :=
    (hoff 0 2).mpr (Or.inr (Or.inr (Or.inl (by norm_num))))
  have hD : (secondOrderDefectGraph G).Adj (u 0).1 (u 2).1 := hDsub
  have h01sub : (G.induce c.supp).Adj (u 0) (u 1) := by
    rw [← (G.induce c.supp).mem_neighborFinset, hu]
    norm_num
  have h21sub : (G.induce c.supp).Adj (u 2) (u 1) := by
    rw [← (G.induce c.supp).mem_neighborFinset, hu]
    norm_num
  have h02 : (u 0).1 ≠ (u 2).1 := by
    intro h
    have h' : (0 : ZMod 8) = 2 := huinj (Subtype.ext h)
    exact (by decide : (0 : ZMod 8) ≠ 2) h'
  exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree h02
    h01sub h21sub) hD

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_lowParameter_false
