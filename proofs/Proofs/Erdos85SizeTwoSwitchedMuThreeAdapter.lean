import Proofs.Erdos85SizeTwoSwitchedJointExtension
import Proofs.Erdos85BinarySquareMuThreeLocalInterface
import Proofs.Erdos85BinarySquareMuThreeExteriorGridEmbedding
import Proofs.Erdos85OrderSixtyFourMuThreeJointEigenlineCapstone

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

/-- In fact the same switched witness supplies the full injective exterior
grid labeling, not only its pointwise signed-pair shadow. -/
theorem orderSixtyFour_sizeTwo_switched_muThree_exterior_gridEmbedding
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
    (s : V → ℤ) (hs : IsAmbientSignedJoint G c 3 s) :
    ∃ label : {u : V // u ∉ c.supp} →
        {z : V // z ∈ c.supp ∧ s z = 1} ×
          {z : V // z ∈ c.supp ∧ s z = -1},
      Function.Injective label ∧
      ∀ u, G.Adj u.1 (label u).1.1 ∧ G.Adj u.1 (label u).2.1 := by
  rcases hs with ⟨hs_out, hs_in, hH, hD⟩
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s 3 hs_out hs_in hH hD
  exact orderSixtyFour_signedSizeTwo_muThree_exterior_gridEmbedding
    G hfree hreg hcard c hc s hs_in hs_out P.sum_eq_zero P.defectAction
      P.ambientAction_in P.ambientAction_out

/-- A checked `K`-symmetry classification closes a switched ambient `μ=3`
witness through the existing joint-eigenline capstone. -/
theorem false_of_orderSixtyFour_sizeTwo_switched_muThree
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
    (classification : MuThreeKSymmetryClassification
      (orderSixtyFourMuThreeInternalRel G (cSupp := c.supp) (s := s))) :
    False := by
  rcases hs with ⟨hs_out, hs_in, hH, hD⟩
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s 3 hs_out hs_in hH hD
  exact false_of_orderSixtyFour_mu3_jointEigenline
    G hfree hreg hcard c hc s hs_in hs_out P.sum_eq_zero P.defectAction
      P.ambientAction_in P.ambientAction_out classification

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_switched_muThree_exterior_signedPair_dichotomy
#print axioms Erdos85.orderSixtyFour_sizeTwo_switched_muThree_exterior_gridEmbedding
#print axioms Erdos85.false_of_orderSixtyFour_sizeTwo_switched_muThree
