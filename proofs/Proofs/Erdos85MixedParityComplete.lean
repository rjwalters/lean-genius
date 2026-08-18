import Proofs.Erdos85MixedComplementEven

/-!
# Unconditional mixed projected-anchor parity
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Complete mixed three-point parity theorem.** The complement-even
hypothesis is discharged by the global block decomposition. -/
theorem odd_mixedProjectedAnchor_iff_threePoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (hcountOdd : Odd (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card)
    (b : ZMod p) (hb : b + b = 1) (s : ZMod p) :
    Odd (mixedProjectedAnchor G u p s) ↔
      s ∉ ({0, b, -b} : Finset (ZMod p)) := by
  apply odd_mixedProjectedAnchor_iff_threePoint_of_complement_even G hfree
    hd heven hmin hcard hp hp7 u hu huRange huD hℓ3 hodd hcountOdd b hb
  intro x
  exact even_sum_mixedComplementFiber G hfree hd heven hmin hcard hp u hu
    huRange huD hℓ3 hodd (2 * x)

end

end Erdos85
