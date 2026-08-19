import Proofs.Erdos85EightEightConcreteTerminalAssembly
import Proofs.Erdos85OrderSixtyFourSizeSixteenOutsideFeasibility

/-!
# Order-64 concrete assembly for the `8+8` branch

The generic concrete terminal still exposes four outside-feasibility inputs.
In the seven-defect-component order-64 branch those inputs follow uniformly
from the unique sixteen-component feasibility package, so only the high
parameter-six owner terminal remains as a callback.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The order-64 seven-component `8+8` branch is impossible once its checked
high-owner terminal is available.  All outside cardinality and pair-map facts
are discharged from the global seven-component feasibility theorem. -/
theorem orderSixtyFour_seven_components_eightEight_false_of_high_terminal
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
  exact binarySquare_regular_sizeTwoPart_eight_eightEight_false_of_high_terminal
    G hfree hreg (by norm_num) c hc s hs_in hs_out hA_in hDs
      a b ha hb hab u v huinj hvinj hurange hvrange hu hv
      hpaircard hpairinc houtcard hRedgesNcard h6

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_seven_components_eightEight_false_of_high_terminal
