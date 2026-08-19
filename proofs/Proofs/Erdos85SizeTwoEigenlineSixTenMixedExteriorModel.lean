import Proofs.Erdos85SizeTwoEigenlineSixTenAllTriangleHighExteriorCoordinates
import Proofs.Erdos85SizeTwoEigenlineSixTenMixedExteriorCoordinates

/-! # Complete exterior-pair model of the genuine mixed six-plus-ten branch -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Full fixed owner relation in the genuine mixed `C6 ⊔ C10` branch:
three short antipodes, fifteen long pairs at offsets `{±1,5}`, and thirty
opposite-sign cross pairs. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_mixed_exteriorPair_model
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
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (hball : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    (∀ i j, (exteriorPairGraph G c.supp).Adj (u i) (u j) ↔
        j - i = 3) ∧
      (∀ i j, (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
        j - i = 1 ∨ j - i = 5 ∨ j - i = 9) ∧
      (∀ i j, (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
        s (v j).1 = -s (u i).1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      binarySquare_regular_sizeTwoPart_eight_sixTen_shortExteriorPair_iff_antipodal
        G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
          u huinj hurange hu
  · exact
      binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_high_exteriorPair_iff
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
          v hvinj hvrange hv hball
  · exact
      binarySquare_regular_sizeTwoPart_eight_sixTen_crossExteriorPair_iff_sign_neg
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
          u v huinj hvinj hurange hvrange hu hv

end


end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_mixed_exteriorPair_model
