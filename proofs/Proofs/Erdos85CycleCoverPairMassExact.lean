import Proofs.Erdos85CycleCoverPairMass

/-!
# Exact quotient-facing cyclic-cover pair mass
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- A reverse quotient entry equal to one gives the exact divisibility
formula for the source component's pair mass. -/
theorem sum_anchorPairMultiplicity_of_componentQuotient_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (hone : componentQuotientMatrix G (secondOrderDefectGraph G) e c = 1)
    (δ : ZMod n) :
    (∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ) =
      if r ∣ δ.val then n else 0 := by
  obtain ⟨f, hadj, horient⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one G hfree hd heven hmin
      hcard hr hn c e u v huinj hvinj huRange hvRange huD hvD hone
  exact sum_anchorPairMultiplicity_of_cycleCover_eq_ite_dvd
    G u v f hadj horient δ

end

end Erdos85
