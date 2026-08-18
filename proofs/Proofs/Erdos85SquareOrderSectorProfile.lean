import Proofs.Erdos85SquareOrderHighIncidence

/-!
# Exhaustive parameterized sector profile at square order

A normalized square-order core has only degrees `d` and `d+1`.  Its
nonregular sector is not a finite list independent of `d`: the number of high
vertices can grow.  This file packages the exact uniform information which is
available without making a finite-classification assumption.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The number of high neighbors of a vertex in a square-order core. -/
def squareOrderHighIncidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (x : V) : ℕ :=
  (G.neighborFinset x ∩ squareOrderHighVertices G d).card

/-- The scale-stable data defining the nonregular square-order sector.

Unlike an orbit table at a fixed order, this profile is exhaustive for every
`d`.  It records the degree dichotomy, independence of the high set, the exact
first two incidence moments, the pointwise low-incidence bound, handshake
parity, and the resulting polynomial bound on the high count. -/
structure SquareOrderNonregularSectorProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop where
  high_nonempty : (squareOrderHighVertices G d).Nonempty
  degree_dichotomy : ∀ x : V,
    G.degree x = d ∨ G.degree x = d + 1
  high_independent : ∀ ⦃x y : V⦄,
    x ∈ squareOrderHighVertices G d →
    y ∈ squareOrderHighVertices G d → ¬ G.Adj x y
  high_parity : Even (d * d * d + (squareOrderHighVertices G d).card)
  first_moment :
    (∑ x : V, squareOrderHighIncidenceCount G d x) =
      (d + 1) * (squareOrderHighVertices G d).card
  second_moment :
    (∑ x : V, (squareOrderHighIncidenceCount G d x) ^ 2) =
      (squareOrderHighVertices G d).card *
        ((squareOrderHighVertices G d).card + d)
  low_incidence_bound : ∀ ⦃x : V⦄, G.degree x = d →
    2 * squareOrderHighIncidenceCount G d x ≤ d
  high_count_bound :
    let h := (squareOrderHighVertices G d).card
    h * h + (3 * d + 1) * h ≤ d * d * d

/-- Every tight-edge-cover square-order core is either regular or belongs to
the parameterized nonregular profile above.  This is the honest exhaustive
sector split; it makes no fixed-order or finite-orbit assumption. -/
theorem squareOrder_regular_or_nonregularSectorProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    (∀ x : V, G.degree x = d) ∨
      SquareOrderNonregularSectorProfile G d := by
  classical
  let H := squareOrderHighVertices G d
  by_cases hH : H = ∅
  · left
    intro x
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard x with hx | hx
    · exact hx
    · exfalso
      have hxH : x ∈ H := by
        simp [H, squareOrderHighVertices, hx]
      rw [hH] at hxH
      exact Finset.notMem_empty x hxH
  · right
    have hnonempty : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hH
    have hpos : 0 < (squareOrderHighVertices G d).card := by
      simpa [H] using hnonempty.card_pos
    refine
      { high_nonempty := by simpa [H] using hnonempty
        degree_dichotomy := fun x =>
          squareOrder_degree_eq_or_succ_of_tightEdgeCover
            G hfree hd hmin hcover hcard x
        high_independent := ?_
        high_parity := squareOrder_even_cube_add_card_high
          G hfree hd hmin hcover hcard
        first_moment := by
          simpa [squareOrderHighIncidenceCount] using
            squareOrder_sum_highNeighborCount_eq G d
        second_moment := by
          simpa [squareOrderHighIncidenceCount] using
            squareOrder_sum_highNeighborCount_sq_eq
              G hfree hd hmin hcover hcard
        low_incidence_bound := ?_
        high_count_bound := squareOrder_high_count_polynomial_bound
          G hfree hd hmin hcover hcard hpos }
    · intro x y hx hy
      have hxdeg : G.degree x = d + 1 :=
        (Finset.mem_filter.mp hx).2
      have hydeg : G.degree y = d + 1 :=
        (Finset.mem_filter.mp hy).2
      exact squareOrder_not_adj_degree_succ_of_tightEdgeCover
        G hcover hxdeg hydeg
    · intro x hx
      simpa [squareOrderHighIncidenceCount] using
        squareOrder_two_mul_highNeighborCount_le_degree
          G hfree hd hmin hcover hcard hx

end

end Erdos85
