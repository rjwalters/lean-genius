import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphFormula
import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerNonzero

/-! # Honest h305 graph contradiction from a matching UNSAT result -/

open Finset SimpleGraph

namespace Erdos85

open Std Sat

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

/-- The structural graph data contradicts any UNSAT proof for its exact
canonical corrected owner CNF.  The certificate module supplies this final
argument separately for each of the six Boolean cases. -/
theorem muNegThreeZeroFiveCorrect_graph_false_of_exterior_of_unsat
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
    (hmodeu : if uTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) v)
    (hunsat : (muNegThreeZeroFiveCorrectOwnerSatCnf uTri vTri
      (muNegOneSigmaOf su sv)).Unsat) : False := by
  let val := muNegThreeZeroFiveCorrectValOfRelations uTri vTri
    (muNegThreeZeroFiveCorrectDGraph G c u v)
    (muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri)
  have hformula : dimacsFormulaSatisfied val
      (muNegThreeZeroFiveCorrectOwnerDimacsClauses uTri vTri
        (muNegOneSigmaOf su sv)) :=
    muNegThreeZeroFiveCorrect_graph_formulaSatisfied_of_exterior
      G c hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange
      hu hv su sv hsu hsv hflipu hflipv hcross uTri vTri hmodeu hmodev
  have hnz := muNegThreeZeroFiveCorrectOwnerDimacsClauses_nonzero_of_mem
    uTri vTri (muNegOneSigmaOf su sv)
  have hsat : (muNegThreeZeroFiveCorrectOwnerSatCnf uTri vTri
      (muNegOneSigmaOf su sv)).Sat (satAssignmentOfDimacs val) := by
    simpa only [muNegThreeZeroFiveCorrectOwnerSatCnf] using
      satCnf_of_dimacsFormulaSatisfied hnz hformula
  have hu := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hu
  contradiction

end


end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrect_graph_false_of_exterior_of_unsat
