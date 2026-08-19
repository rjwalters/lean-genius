import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalTriangles

/-!
# Rooted antipodal-triangle census in the high eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The eight directed half-turn bases on the first C8 support at least
thirty-two rooted antipodal triples.  Swapping the two cycles gives the same
bound on the second shore, hence at least sixty-four across both shores. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_rootedAntipodalTriangles_sum_ge
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
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hab6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6) :
    32 ≤ ∑ i : ZMod 8,
      ((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b (u i)) ∩
        componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b
            (u (i + 4))).card := by
  have hlocal : ∀ i : ZMod 8, 4 ≤
      ((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b (u i)) ∩
        componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b
            (u (i + 4))).card := by
    intro i
    exact (binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv hab6 i).2.1
  calc
    32 = ∑ _i : ZMod 8, 4 := by
      norm_num [Finset.sum_const, Nat.card_zmod]
    _ ≤ ∑ i : ZMod 8,
        ((componentNeighborFinset
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b (u i)) ∩
          componentNeighborFinset
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b
              (u (i + 4))).card := Finset.sum_le_sum fun i _ => hlocal i

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_rootedAntipodalTriangles_sum_ge
