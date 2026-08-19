import Proofs.Erdos85SizeTwoSwitchedJointExtension
import Proofs.Erdos85BinarySquareMuThreeLocalInterface

/-! # Feeding a switched ambient witness into the μ=3 exterior route -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The bundled ambient witness produced by a shore switch has exactly the
local interface required by the existing μ=3 exterior signed-pair
dichotomy. -/
theorem orderSixtyFour_sizeTwo_switched_muThree_exterior_signedPair_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ) (hs : IsAmbientSignedJoint G c 3 s)
    (u : V) (hu : u ∉ c.supp) :
    ∃ z z' : V,
      s z = 1 ∧ s z' = -1 ∧ z ∈ c.supp ∧ z' ∈ c.supp ∧ z ≠ z' ∧
      ((G.Adj z z' → ∀ y, G.Adj u y → y ∉ c.supp →
          ¬ G.Adj z y ∧ ¬ G.Adj z' y) ∧
       (¬ G.Adj z z' →
          (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z y) ∧
          (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z' y))) := by
  rcases hs with ⟨hs_out, hs_in, hH, hD⟩
  exact orderSixtyFour_sizeTwo_muThree_exterior_signedPair_dichotomy_of_local
    G hfree hreg hcard c hc s hs_out hs_in hH hD u hu

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_switched_muThree_exterior_signedPair_dichotomy
