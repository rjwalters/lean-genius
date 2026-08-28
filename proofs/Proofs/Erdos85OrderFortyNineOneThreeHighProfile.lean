import Proofs.Erdos85OrderFortyNineGeneralHighProfile

/-!
# The one- and three-high incidence profiles

The universal global profile collapses the smallest high-count strata.  At
one high there is a unique incidence distribution.  At three highs there
are exactly two, corresponding to the empty triple system and the unique
triple on all three high points.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The unique high-incidence profile when there is one high vertex. -/
theorem orderFortyNine_highIncidence_profile_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1) :
    let n := orderFortyNineHighIncidenceCount G
    n 0 = 40 ∧ n 1 = 8 ∧ n 2 = 0 ∧ n 3 = 0 := by
  dsimp only
  have hp := orderFortyNine_highIncidence_general_profile
    G hfree hmin hcard
  dsimp only at hp
  rw [hHigh] at hp
  omega

/- The three-high profile theorem formerly declared here was superseded by the
statement-identical `orderFortyNine_highIncidence_profile_of_three_high` in
`Erdos85OrderFortyNineHighIncidenceCensus` (736d58e95a), which all consumers
import.  The duplicate declaration broke whole-library builds
(`lake build lratreplay`, 2026-08-28) and was removed; the one-high profile
above remains this module's unique content. -/

end

end Erdos85
