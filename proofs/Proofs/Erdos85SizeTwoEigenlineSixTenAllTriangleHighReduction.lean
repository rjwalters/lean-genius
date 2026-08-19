import Proofs.Erdos85SizeTwoEigenlineSixTenAllTriangleLowExclusion

/-!
# Reduction of the all-triangle `6+10` branch to the high support

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The distance-two obstruction eliminates the low member of the long-shore
shape dichotomy, leaving only antipodal offsets `{±3, ±4}`. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_high_support
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
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hball : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0) :
    ∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
      j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7 := by
  rcases
      binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_antipodal_shape
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
          v hvinj hvrange hv hball with hlow | hhigh
  · exfalso
    apply binarySquare_regular_sizeTwoPart_eight_sixTen_not_long_support_two_three
      G hfree c v hvinj hv
    intro i j
    rw [binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_defectAdj_iff_antipodal
      G c b hball (v i) (v j)]
    · exact hlow i j
    · rw [← hvrange]
      exact ⟨i, rfl⟩
  · exact hhigh

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_high_support
