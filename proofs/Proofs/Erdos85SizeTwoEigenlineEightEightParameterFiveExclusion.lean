import Proofs.Erdos85SizeTwoEigenlineEightEightParameterFiveDiagonalShape

/-!
# Excluding the 8+8 parameter-five branch

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

In the coordinated 8+8 stratum with cross quotient `5`, the diagonal
defect block of an all-triangle shore is forced to the offsets `{±2}`
(`…parameterFive_firstCycle_defectAdj_iff_offset_two_six`).  But a
distance-two pair of the ambient C8 has the intervening cycle vertex as
a common neighbour, so it can never be a second-order defect pair — the
same five-line midpoint contradiction that killed the low 6+10 support.
Hence the parameter-five branch is impossible outright.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **Parameter-five exclusion.**  A coordinated 8+8 size-two eigenline
component with cross quotient `5` and an all-triangle first shore is
impossible: its forced `{±2}` diagonal defect offsets contradict the
midpoint common neighbour. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFive_false
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
    (hab5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 5)
    (haall : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0) :
    False := by
  have hoff :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFive_firstCycle_defectAdj_iff_offset_two_six
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv hab5 haall
  have hDsub : ((secondOrderDefectGraph G).induce c.supp).Adj (u 0) (u 2) :=
    (hoff 0 2).mpr (Or.inl (by norm_num))
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

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFive_false
