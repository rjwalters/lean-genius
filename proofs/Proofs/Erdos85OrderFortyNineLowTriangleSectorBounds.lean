import Proofs.Erdos85OrderFortyNineLowTriangleIncidenceDivisibility
import Proofs.Erdos85OrderFortyNineFiveHighTripleBound

/-! Sector-wide lower bounds for actual all-low triangle incidence.
These sharpen the minimum-incidence exclusions; no sector is excluded. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every order49 C4-free minimum7 graph with three high vertices has at
least27 all-low local triangle incidences, without a support-profile premise. -/
theorem orderFortyNine_threeHigh_lowLow_sum_ge_27
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49)
    (hh : (orderFortyNineHighVertices G).card = 3) :
    27 ≤ ∑ v ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G v := by
  have hc := orderFortyNine_highIncidence_census G hfree hmin hcard
  rw [hh] at hc
  have hn0 : 24 ≤ orderFortyNineHighIncidenceCount G 0 := by omega
  by_cases hz : orderFortyNineHighIncidenceCount G 0 = 24
  · exact orderFortyNine_threeHigh_lowLow_sum_ge_twentySeven G hfree hmin hcard hh hz
  · have hb := orderFortyNine_empty_count_le_lowLow_sum G hfree hmin hcard
    have hd := orderFortyNine_three_dvd_lowLow_sum G hfree hmin hcard
    omega

/-- Every order49 C4-free minimum7 graph with five high vertices has at
least15 all-low local triangle incidences, without a support-profile premise. -/
theorem orderFortyNine_fiveHigh_lowLow_sum_ge_15
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49)
    (hh : (orderFortyNineHighVertices G).card = 5) :
    15 ≤ ∑ v ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G v := by
  have hc := orderFortyNine_highIncidence_census G hfree hmin hcard
  rw [hh] at hc
  have ht := orderFortyNine_highIncidenceCount_three_le_two_of_five_high G hfree hh
  have hn0 : 12 ≤ orderFortyNineHighIncidenceCount G 0 := by omega
  by_cases hz : orderFortyNineHighIncidenceCount G 0 = 12
  · exact orderFortyNine_fiveHigh_lowLow_sum_ge_fifteen G hfree hmin hcard hh hz
  · have hb := orderFortyNine_empty_count_le_lowLow_sum G hfree hmin hcard
    have hd := orderFortyNine_three_dvd_lowLow_sum G hfree hmin hcard
    omega
end Erdos85
