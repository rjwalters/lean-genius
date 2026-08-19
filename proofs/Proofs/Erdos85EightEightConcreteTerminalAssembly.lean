import Proofs.Erdos85EightEightLowParameterFourTerminal
import Proofs.Erdos85EightEightMixedParameterFourTerminal
import Proofs.Erdos85EightEightBothTriangleParameterFourTerminal

/-!
# Concrete terminal assembly for the `8+8` stratum

All parameter-four sectors are now closed by checked owner certificates.
This wrapper plugs those concrete callbacks into the structural terminal
tree and leaves only the parameter-six high-owner callback exposed.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Once the high `r=6` callback is supplied, the entire `8+8` stratum is
impossible.  The three `r=4` callbacks are discharged internally. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_false_of_high_terminal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hVcard : Fintype.card V = 8 * 8)
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
    (hpaircard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hpairinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (houtcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedgesNcard : (exteriorPairGraph G c).edgeSet.ncard = 48)
    (h6 : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 1 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 6 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 1 →
      EightEightShoreAllTriangle G c a →
      EightEightShoreAllTriangle G c b → False) :
    False := by
  apply binarySquare_regular_sizeTwoPart_eight_eightEight_false_of_terminals
    G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
      u v huinj hvinj hurange hvrange hu hv
  · intro haa3 hab4 hba4 hbb3 htfA htfB
    exact binarySquare_regular_sizeTwoPart_eight_eightEight_low_parameterFour_false
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b hab
        u v huinj hvinj hurange hvrange hu hv haa3 hab4 hba4 hbb3
        htfA htfB hpaircard hpairinc houtcard hRedgesNcard
  · intro haa3 hab4 hba4 hbb3 hmixed
    exact binarySquare_regular_sizeTwoPart_eight_eightEight_mixed_parameterFour_false
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv hab4 hba4 haa3 hbb3
        hmixed hpaircard hpairinc houtcard hRedgesNcard
  · intro haa3 hab4 _hba4 hbb3 hallA hallB
    exact binarySquare_regular_sizeTwoPart_eight_eightEight_bothTriangle_parameterFour_false
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b hab
        u v huinj hvinj hurange hvrange hu hv hallA hallB haa3 hbb3
        hab4 hpaircard hpairinc houtcard hRedgesNcard
  · exact h6

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_false_of_high_terminal
