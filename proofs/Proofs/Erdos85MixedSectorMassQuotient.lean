import Proofs.Erdos85MixedNonsquareMass
import Proofs.Erdos85DifferenceArrayBoundary

/-!
# Quotient interpretation of the mixed selected-sector anchor mass
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- The selected-sector anchor mass is exactly the partial diagonal trace of
the second-order component quotient over the `p`-divisible components. -/
theorem pDivisibleAnchorMass_eq_sum_diagonalQuotient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp) :
    pDivisibleAnchorMass G u p =
      ∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ c.supp.ncard),
          componentQuotientMatrix G (secondOrderDefectGraph G) c c := by
  unfold pDivisibleAnchorMass
  apply Finset.sum_congr rfl
  intro c hc
  exact card_graphCycleBlockZeroSupport_eq_componentQuotient G hfree hd
    heven hmin hcard c c (u c) (u c) (hu c) (huRange c) (huRange c)

end

end Erdos85
