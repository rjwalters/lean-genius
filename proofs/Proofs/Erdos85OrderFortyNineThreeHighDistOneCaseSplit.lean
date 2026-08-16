import Proofs.Erdos85OrderFortyNineDistOnePinning

/-!
# Exhaustive cases for the distinct-root three-high geometry

The historical `b1/c1/c2` names correspond respectively to a paired pair of
first-root witnesses with no sibling coincidence, an unpaired pair with no
coincidence, and an unpaired pair with exactly one coincidence.  This module
turns that informal classification into a reusable Lean theorem.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The distinct-root geometry has exactly the three cases used by the
order-49 survivor analysis.  The impossible paired/coincidence combination
is removed internally by the C4 argument already proved in
`orderFortyNineDistOne_partner_forces_no_sibling_coincidence`. -/
theorem orderFortyNine_threeHigh_distinctRoot_b1_c1_c2_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 u12 u13 u23 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (hu12u13 : u12 ≠ u13) (hu12u23 : u12 ≠ u23)
    (hu13u23 : u13 ≠ u23)
    (hu12_1 : G.Adj u12 v1) (hu12_2 : G.Adj u12 v2)
    (hu13_1 : G.Adj u13 v1) (hu13_3 : G.Adj u13 v3)
    (hu23_2 : G.Adj u23 v2) (hu23_3 : G.Adj u23 v3) :
    ∃ x2 x3 : V,
      G.degree x2 = 7 ∧ G.degree x3 = 7 ∧
      G.Adj u12 x2 ∧ G.Adj v2 x2 ∧
      G.Adj u13 x3 ∧ G.Adj v3 x3 ∧
      ((G.Adj u12 u13 ∧ x2 ≠ u23 ∧ x3 ≠ u23) ∨
       (¬ G.Adj u12 u13 ∧
          ((x2 = u23 ∧ x3 ≠ u23) ∨
           (x2 ≠ u23 ∧ x3 = u23))) ∨
       (¬ G.Adj u12 u13 ∧ x2 ≠ u23 ∧ x3 ≠ u23)) := by
  obtain ⟨x2, x3, hx2deg, hx3deg, hx2u12, hx2v2,
      hx3u13, hx3v3, _hx2Branch, _hx3Branch, hcoincidence⟩ :=
    orderFortyNineDistOne_exists_siblings_and_coincidence_split
      G hfree hmin hcard hv1 hv2 hv3 h12 h13 hu12u13
      hu12_1 hu12_2 hu13_1 hu13_3 hu23_2 hu23_3
  refine ⟨x2, x3, hx2deg, hx3deg, hx2u12, hx2v2,
    hx3u13, hx3v3, ?_⟩
  by_cases hpair : G.Adj u12 u13
  · have hnone := orderFortyNineDistOne_partner_forces_no_sibling_coincidence
      G hfree hmin hcard hv1 hv2 hv3
      hu12_1 hu12_2 hu13_1 hu13_3 hu23_2 hu23_3 hpair
      hx2u12 hx3u13 hu12u23 hu13u23
    exact Or.inl ⟨hpair, hnone.1, hnone.2⟩
  · rcases hcoincidence with h2 | h3 | hnone
    · exact Or.inr (Or.inl ⟨hpair, Or.inl h2⟩)
    · exact Or.inr (Or.inl ⟨hpair, Or.inr h3⟩)
    · exact Or.inr (Or.inr ⟨hpair, hnone.1, hnone.2⟩)

end

end Erdos85
