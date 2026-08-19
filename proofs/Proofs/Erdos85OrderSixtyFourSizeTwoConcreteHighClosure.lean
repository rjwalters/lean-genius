import Proofs.Erdos85OrderSixtyFourSizeTwoConcreteAssembly
import Proofs.Erdos85EightEightHighConcreteTerminal

/-! # Closing the order-64 size-two high branch -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The order-64 seven-component size-two eigenline is impossible with no
remaining high-owner callback: its quotient-six leaf is discharged by the
normalized concrete exterior model. -/
theorem orderSixtyFour_seven_components_sizeTwoEigenline_false
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : Fin 64 → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x) : False := by
  have hmin : ∀ x : Fin 64, 8 ≤ G.degree x := by
    intro x
    rw [hreg x]
  have hcover : ∀ {x y : Fin 64}, G.Adj x y →
      G.degree x = 8 ∨ G.degree y = 8 := by
    intro x y _hxy
    exact Or.inl (hreg x)
  obtain ⟨hpaircard, hpairinc, houtcard, hRedgesNcard⟩ :=
    orderSixtyFour_sizeSixteen_outsidePair_feasibility
      G hfree hmin hcover hcount c (by simpa using hc)
  apply false_of_sizeTwoEigenline_eight_of_stratum_terminals
    G hfree hreg (by norm_num) c hc s hs_in hs_out hsum hA_in
      (by simpa using hDs)
  · intro a b hab hshape
    obtain ⟨ha, hb, _haa, _habq, _hbaq, _hbb⟩ := hshape
    exact binarySquare_regular_sizeTwoPart_eight_sixTen_false
      G hfree hreg (by norm_num) c hc s hs_in hs_out hA_in hDs
        a b hab ha hb hpaircard hpairinc houtcard hRedgesNcard
  · intro a b hab hshape
    obtain ⟨ha, hb, _r, _hr2, _hr7, _haa, _habq, _hbaq, _hbb⟩ := hshape
    apply orderSixtyFour_seven_components_eightEight_false_of_abstract_high_terminal
      G hfree hreg hcount c hc s hs_in hs_out hA_in hDs a b ha hb hab
    intro _haa hab6 hba6 _hbb _allA _allB
    exact binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_high_false
      G hfree hreg (by norm_num) c hc s hs_in hs_out hA_in hDs
        a b ha hb hab hab6 hba6 hpaircard hpairinc houtcard hRedgesNcard

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_seven_components_sizeTwoEigenline_false
