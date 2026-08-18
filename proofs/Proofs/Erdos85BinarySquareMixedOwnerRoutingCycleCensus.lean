import Proofs.Erdos85BinarySquareMixedOwnerRootedRoutingCycles

/-! # Global census of prescribed mixed-owner routing cycles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- All rooted `(a,b,c)` routing cycles, retaining the root in a sigma type so
that each cyclic incidence is counted once for each specified root. -/
def allDistinctRoutingCycles
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent) :
    Finset (Σ _x : Fin 64, Fin 64 × Fin 64) :=
  Finset.univ.sigma fun x =>
    rootedAllDistinctRoutingCyclePairs G hfree a b c x

/-- The global routing-cycle census is the sum of its rooted fibers. -/
theorem card_allDistinctRoutingCycles_eq_sum_rooted
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent) :
    (allDistinctRoutingCycles G hfree a b c).card =
      ∑ x : Fin 64,
        (rootedAllDistinctRoutingCyclePairs G hfree a b c x).card := by
  classical
  rw [allDistinctRoutingCycles, Finset.card_sigma]

/-- The pointwise lower bound therefore supplies at least `64 * 12 = 768`
rooted prescribed routing-cycle incidences for every ordered triple of
distinct owner colors. -/
theorem orderSixtyFour_regular_fourComponents_allDistinctRoutingCycles_card_ge
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    768 ≤ (allDistinctRoutingCycles G hfree a b c).card := by
  rw [card_allDistinctRoutingCycles_eq_sum_rooted]
  calc
    768 = ∑ _x : Fin 64, 12 := by norm_num
    _ ≤ ∑ x : Fin 64,
        (rootedAllDistinctRoutingCyclePairs G hfree a b c x).card := by
      apply Finset.sum_le_sum
      intro x _hx
      exact
        orderSixtyFour_regular_fourComponents_rootedAllDistinctRoutingCyclePairs_card_ge
          G hfree hreg hcount a b c hab hac hbc x

end

end Erdos85
