import Proofs.Erdos85MuNegThreeZeroFiveCorrectFiniteTerminal
import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphSemantics
import Proofs.Erdos85MuNegThreeZeroFiveCrossCountFields

/-! # Checked graph terminal for the honest 88-owner h305 endpoint -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- The honest h305 exterior geometry is impossible in each of its three
canonical shore-mode cases. -/
theorem muNegThreeZeroFiveCorrect_graph_false_of_exterior
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hflipu : ∀ i, su (i + 1) = -su i)
    (hflipv : ∀ j, sv (j + 1) = -sv j)
    (hcross : MuNegThreeZeroFiveCrossExteriorSplit
      (exteriorPairGraph G c.supp) u v su sv)
    (uTri vTri : Bool)
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true))
    (hmodeu : if uTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) v) :
    False := by
  have hphase := zmodEight_two_alternating_sign_phase_routing su sv
    hsu hsv hflipu hflipv
  obtain ⟨hrowSame, hrowOpp, hcolSame, hcolOpp⟩ :=
    muNegThreeZeroFive_crossDefect_count_fields
      (exteriorPairGraph G c.supp) u v su sv hsu hsv hphase hcross
  exact muNegThreeZeroFiveCorrectFiniteSemantics_false hcanon
    hrowSame hrowOpp hcolSame hcolOpp
    (muNegThreeZeroFiveCorrect_nonCrossSemantics_graph
      G c hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange
      hu hv uTri vTri (muNegOneSigmaOf su sv) hmodeu hmodev)

end


end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrect_graph_false_of_exterior
