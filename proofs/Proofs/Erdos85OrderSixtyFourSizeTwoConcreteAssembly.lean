import Proofs.Erdos85SizeTwoEigenlineTerminalAssembly
import Proofs.Erdos85EightEightNormalizedCoordinates
import Proofs.Erdos85SixTenNormalizedCoordinates

/-!
# Concrete order-64 assembly for a size-two eigenline component

The structural top-level theorem splits the internal sixteen-vertex graph
into its connected branch, a `6+10` branch, and an `8+8` branch.  The first
is already contradictory.  This module plugs the concrete order-64 `8+8`
assembly into that split, exposing only the checked high-owner leaf and the
parallel `6+10` terminal.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An order-64 seven-component size-two eigenline is impossible once the
remaining `6+10` terminal and the parameter-six high-owner leaf are known.
The connected and all other `8+8` branches are discharged internally. -/
theorem orderSixtyFour_seven_components_sizeTwoEigenline_false_of_terminals
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
      3 * s x)
    (hHigh : ∀ (a b : (G.induce c.supp).ConnectedComponent), a ≠ b →
      componentQuotientMatrix
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
    exact orderSixtyFour_seven_components_eightEight_false_of_abstract_high_terminal
      G hfree hreg hcount c hc s hs_in hs_out hA_in hDs a b ha hb hab
        (hHigh a b hab)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_seven_components_sizeTwoEigenline_false_of_terminals
