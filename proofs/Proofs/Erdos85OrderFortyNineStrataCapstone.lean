import Proofs.Erdos85OrderFortyNineNineHighContradiction

/-!
# Order-49 stratum capstone

This file is the final integration socket for the remaining order-49
certificate families.  The nine-high stratum is already closed internally;
the other four inputs are precisely the exclusions still being discharged.
-/

namespace Erdos85

open SimpleGraph

/-- A uniform proposition saying that the `h`-high order-49 stratum is
empty.  Restricting to `Fin 49` matches the concrete witness definition and
keeps computational certificate terminals free of transport boilerplate. -/
def OrderFortyNineStratumExcluded (h : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = h → False

theorem orderFortyNineStratumExcluded_nine :
    OrderFortyNineStratumExcluded 9 := by
  intro G _ _ _ hfree hmin hHigh
  exact false_of_orderFortyNine_nine_high
    G hfree hmin (Fintype.card_fin 49) hHigh

/-- Once the four remaining odd high-count strata are excluded, no
order-49 minimum-degree-seven C4-free witness exists. -/
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata
    (h1 : OrderFortyNineStratumExcluded 1)
    (h3 : OrderFortyNineStratumExcluded 3)
    (h5 : OrderFortyNineStratumExcluded 5)
    (h7 : OrderFortyNineStratumExcluded 7) :
    ¬ C4FreeMinDegreeWitness 49 7 := by
  rintro ⟨G, hdec, hminDegree, hfree⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  have hmin : ∀ x : Fin 49, 7 ≤ G.degree x := fun x =>
    hminDegree.trans (G.minDegree_le_degree x)
  rcases orderFortyNine_card_high_eq_one_or_three_or_five_or_seven_or_nine
      G hfree hmin (Fintype.card_fin 49) with
    hh | hh | hh | hh | hh
  · exact h1 G inferInstance inferInstance inferInstance hfree hmin hh
  · exact h3 G inferInstance inferInstance inferInstance hfree hmin hh
  · exact h5 G inferInstance inferInstance inferInstance hfree hmin hh
  · exact h7 G inferInstance inferInstance inferInstance hfree hmin hh
  · exact orderFortyNineStratumExcluded_nine
      G inferInstance inferInstance inferInstance hfree hmin hh

end Erdos85
