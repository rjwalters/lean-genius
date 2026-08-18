import Proofs.Erdos85ZModProjectionFiber
import Proofs.Erdos85GraphDiagonalAnchor

/-!
# Negation symmetry of projected graph anchors

Diagonal zero-row supports are inverse closed.  Consequently both their
total anchor multiplicity and every cyclic quotient of that multiplicity
are invariant under coordinate negation.  This is the real-cyclotomic input
needed by the special order-five and order-nine norm arguments.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem graph_anchorMultiplicity_neg_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) (h : ZMod r) :
    anchorMultiplicity
        (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)) (-h) =
      anchorMultiplicity
        (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)) h := by
  apply anchorMultiplicity_neg_eq
  intro c
  exact negFinset_graphCycleBlockZeroSupport_self
    G hfree hd heven hmin hcard hr3 hrOdd (u c) (hu c) (huD c)

theorem graph_projectedAnchorMultiplicity_neg_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r p : ℕ} [NeZero r] [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r) (hpdiv : p ∣ r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) (y : ZMod p) :
    projectedMultiplicity (ZMod.castHom hpdiv (ZMod p))
        (anchorMultiplicity
          (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) (-y) =
      projectedMultiplicity (ZMod.castHom hpdiv (ZMod p))
        (anchorMultiplicity
          (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) y := by
  apply projectedMultiplicity_neg_eq_zmod_castHom hpdiv
  intro h
  exact graph_anchorMultiplicity_neg_eq G hfree hd heven hmin hcard
    hr3 hrOdd u hu huD h

end

end Erdos85
