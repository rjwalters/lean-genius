import Proofs.Erdos85OrderFortyNineNineHighContradiction
import Proofs.Erdos85OrderFortyNineOneThreeHighProfile
import Proofs.Erdos85OrderFortyNineFiveHighTripleBound
import Proofs.Erdos85OrderFortyNineSevenHighProfile

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

/-- Certificate-facing exclusion of one cell in the `(high count, triple
multiplicity)` census.  This is the common semantic endpoint for the
classified SAT instances: `t` counts low vertices adjacent to three highs. -/
def OrderFortyNineTripleCellExcluded (h t : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = h →
    orderFortyNineHighIncidenceCount G 3 = t → False

/-- The two triple-system cells `t=0,1` exhaust the three-high stratum. -/
theorem orderFortyNineStratumExcluded_three_of_tripleCells
    (h0 : OrderFortyNineTripleCellExcluded 3 0)
    (h1 : OrderFortyNineTripleCellExcluded 3 1) :
    OrderFortyNineStratumExcluded 3 := by
  intro G _ _ _ hfree hmin hHigh
  have hp := orderFortyNine_highIncidence_profile_of_three_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  rcases hp with hp | hp
  · exact h0 G inferInstance inferInstance inferInstance hfree hmin hHigh hp.2.2.2
  · exact h1 G inferInstance inferInstance inferInstance hfree hmin hHigh hp.2.2.2

/-- The three triple-system cells `t=0,1,2` exhaust the five-high stratum. -/
theorem orderFortyNineStratumExcluded_five_of_tripleCells
    (h0 : OrderFortyNineTripleCellExcluded 5 0)
    (h1 : OrderFortyNineTripleCellExcluded 5 1)
    (h2 : OrderFortyNineTripleCellExcluded 5 2) :
    OrderFortyNineStratumExcluded 5 := by
  intro G _ _ _ hfree hmin hHigh
  have hp := orderFortyNine_highIncidence_profile_of_five_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  rcases hp with hp | hp | hp
  · exact h0 G inferInstance inferInstance inferInstance hfree hmin hHigh hp.2.2.2
  · exact h1 G inferInstance inferInstance inferInstance hfree hmin hHigh hp.2.2.2
  · exact h2 G inferInstance inferInstance inferInstance hfree hmin hHigh hp.2.2.2

/-- The eight cells `t=0,...,7` exhaust the seven-high stratum. -/
theorem orderFortyNineStratumExcluded_seven_of_tripleCells
    (h0 : OrderFortyNineTripleCellExcluded 7 0)
    (h1 : OrderFortyNineTripleCellExcluded 7 1)
    (h2 : OrderFortyNineTripleCellExcluded 7 2)
    (h3 : OrderFortyNineTripleCellExcluded 7 3)
    (h4 : OrderFortyNineTripleCellExcluded 7 4)
    (h5 : OrderFortyNineTripleCellExcluded 7 5)
    (h6 : OrderFortyNineTripleCellExcluded 7 6)
    (h7 : OrderFortyNineTripleCellExcluded 7 7) :
    OrderFortyNineStratumExcluded 7 := by
  intro G _ _ _ hfree hmin hHigh
  have hp := orderFortyNine_highIncidence_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  have ht : orderFortyNineHighIncidenceCount G 3 ≤ 7 := hp.2.2.2
  interval_cases htval : orderFortyNineHighIncidenceCount G 3
  · exact h0 G inferInstance inferInstance inferInstance hfree hmin hHigh htval
  · exact h1 G inferInstance inferInstance inferInstance hfree hmin hHigh htval
  · exact h2 G inferInstance inferInstance inferInstance hfree hmin hHigh htval
  · exact h3 G inferInstance inferInstance inferInstance hfree hmin hHigh htval
  · exact h4 G inferInstance inferInstance inferInstance hfree hmin hHigh htval
  · exact h5 G inferInstance inferInstance inferInstance hfree hmin hHigh htval
  · exact h6 G inferInstance inferInstance inferInstance hfree hmin hHigh htval
  · exact h7 G inferInstance inferInstance inferInstance hfree hmin hHigh htval

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
