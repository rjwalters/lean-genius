import Proofs.Erdos85OrderSixtyFourBranchReduction

/-! # The two-high order-64 branch -/

open SimpleGraph

namespace Erdos85

/-- In the two-high branch there is a unique vertex incident with both high
vertices.  This canonical double-contact vertex is the pivot for the ensuing
slide-saturation geometry. -/
theorem orderSixtyFour_existsUnique_two_high_contact
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃! x : Fin 64,
      (G.neighborFinset x ∩ squareOrderHighVertices G 8).card = 2 := by
  have hp := orderSixtyFour_two_high_graph_profile G hfree hmin hcover hh
  dsimp only at hp
  let S := Finset.univ.filter fun x : Fin 64 =>
    (G.neighborFinset x ∩ squareOrderHighVertices G 8).card = 2
  have hScard : S.card = 1 := hp.2.1
  obtain ⟨x, hxS⟩ := Finset.card_eq_one.mp hScard
  have hxmem : x ∈ S := by simp [hxS]
  refine ⟨x, (Finset.mem_filter.mp hxmem).2, ?_⟩
  intro y hy
  have hymem : y ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩
  rw [hxS] at hymem
  simpa using hymem

/-- Geometrically, the canonical double-contact vertex is adjacent to the
entire two-vertex high sector, and it is the unique vertex with this property. -/
theorem orderSixtyFour_existsUnique_neighbor_inter_high_eq_high
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃! x : Fin 64,
      G.neighborFinset x ∩ squareOrderHighVertices G 8 =
        squareOrderHighVertices G 8 := by
  obtain ⟨x, hx, hunique⟩ :=
    orderSixtyFour_existsUnique_two_high_contact G hfree hmin hcover hh
  have hxEq : G.neighborFinset x ∩ squareOrderHighVertices G 8 =
      squareOrderHighVertices G 8 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  refine ⟨x, hxEq, ?_⟩
  intro y hy
  apply hunique y
  rw [hy, hh]

/-- The same branch has exactly sixteen single-contact vertices. -/
theorem orderSixtyFour_card_one_high_contact_eq_sixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    (Finset.univ.filter fun x : Fin 64 =>
      (G.neighborFinset x ∩ squareOrderHighVertices G 8).card = 1).card = 16 := by
  have hp := orderSixtyFour_two_high_graph_profile G hfree hmin hcover hh
  exact hp.2.2

end Erdos85
