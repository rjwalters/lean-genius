import Proofs.Erdos85BinarySquareRegularParity

/-!
# Sector uniformity on each internal cycle

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3.

The ambient graph induced on a normalized size-two defect component is a
disjoint union of cycles.  Even when it is not connected, triangle-free
degree status cannot change along one such cycle.  Thus every internal cycle
is wholly all-triangle or wholly triangle-free; any remaining mixed behavior
can occur only between distinct cycles in the irreducible defect quotient.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- On every connected component of the internal ambient two-factor, all
vertices have triangle-free degree zero or all have triangle-free degree two. -/
theorem binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (a : (G.induce c.supp).ConnectedComponent) :
    (∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0) ∨
      (∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2) := by
  classical
  by_cases hseed : ∃ x : c.supp,
      x ∈ a.supp ∧ (triangleFreeEdgeGraph G).degree x.1 = 2
  · right
    obtain ⟨x, hxmem, hx2⟩ := hseed
    intro y hymem
    have hreach : (G.induce c.supp).Reachable x y :=
      a.reachable_of_mem_supp hxmem hymem
    rw [reachable_eq_reflTransGen] at hreach
    induction hreach with
    | refl => exact hx2
    | tail hpath hadj ih =>
        have hprev : _ ∈ a.supp := (a.mem_supp_congr_adj hadj).mpr hymem
        exact (binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_adj
          G hfree hq hqEven hreg hcard c hc _ _ (by simpa using hadj)).mp
            (ih hprev)
  · left
    intro x hxmem
    rcases binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree hq hqEven hreg hcard c hc x with hx0 | hx2
    · exact hx0
    · exact False.elim (hseed ⟨x, hxmem, hx2⟩)

end


end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
