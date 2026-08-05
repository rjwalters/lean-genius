import Proofs.Erdos85EqualCycleResidual

/-!
# Closure of the equal-cycle second-order boundary

The frequency terminals classify every even second-order boundary graph
whose defect cycles have a common length: its degree is `4` or `12`.
Consequently the equal-cycle branch is impossible at every degree at least
thirteen, which is the form needed by an eventual argument.
-/

namespace Erdos85

open SimpleGraph

/-- An even second-order boundary graph of degree at least thirteen cannot
have all defect components of one common order. -/
theorem containsC4_of_even_secondOrder_equalCycles_of_degree_ge_thirteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {d r : ℕ} (hd : 13 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hlen : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) :
    containsC4 V G := by
  by_contra hfree
  have hsmall := equalCycle_degree_eq_four_or_twelve
    G hfree (by omega) hdeven hmin hcard hlen
  omega

end Erdos85
