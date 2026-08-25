import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphService
import Proofs.Erdos85MuNegOneOneFourGraphC4Intertwine

/-! # Graph realization of the corrected h305 non-cross semantics -/

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

/-- Package the honest 88-owner graph laws into the finite semantic
interface consumed by the corrected h305 CNF valuation. -/
theorem muNegThreeZeroFiveCorrect_nonCrossSemantics_graph
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
    (uTri vTri sigma : Bool)
    (hmodeu : if uTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) v) :
    MuNegThreeZeroFiveCorrectNonCrossSemantics uTri vTri sigma
      (muNegThreeZeroFiveCorrectDGraph G c u v)
      (muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri) := by
  refine {
    intertwine := ?_
    hit_active := ?_
    service_exists := muNegThreeZeroFiveCorrect_service_exists_graph
      G c u v uTri vTri hfree hreg hcard hc a b hab huinj hvinj
      hurange hvrange hu hv hmodeu hmodev
    service_unique := muNegThreeZeroFiveCorrect_service_unique_graph
      G c u v uTri vTri hfree hreg hcard hc a b hab huinj hvinj
      hurange hvrange hmodeu hmodev
    c4_intersecting := muNegThreeZeroFiveCorrect_c4_intersecting_graph
      G c u v uTri vTri hfree hreg hcard hc a b hab huinj hvinj
      hurange hvrange
    c4_no_two := muNegThreeZeroFiveCorrect_c4_no_two_graph
      G c u v uTri vTri hfree hreg hcard hc a b hab huinj hvinj
      hurange hvrange }
  · simpa [muNegThreeZeroFiveCorrectDGraph, muNegOneDGraph] using
      (muNegOne_intertwine_graph G c u v hfree hreg a b hab huinj hvinj
        hurange hvrange hu hv)
  · intro aa bb hp hX
    have hbounds :=
      (mem_muNegThreeZeroFiveCorrectHitPairs_iff uTri vTri aa bb).mp hp
    rw [muNegThreeZeroFiveCorrectXGraph_true_iff] at hX
    obtain ⟨haa, hbb, ta, tb, hta, htb, _⟩ := hX
    exact ⟨
      muNegThreeZeroFiveCorrectOwnerActive_of_ownerVertex
        G c u v uTri vTri a b hab hurange hvrange hta,
      muNegThreeZeroFiveCorrectOwnerActive_of_ownerVertex
        G c u v uTri vTri a b hab hurange hvrange htb⟩

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrect_nonCrossSemantics_graph
