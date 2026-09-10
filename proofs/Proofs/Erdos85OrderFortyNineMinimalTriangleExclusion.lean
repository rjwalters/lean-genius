import Proofs.Erdos85OrderFortyNineCubicLowTriangleTrace
import Proofs.Erdos85OrderFortyNineMixedDefectTrace
import Proofs.Erdos85OrderFortyNineSurvivorTriangleLedger

/-! Excluding minimum all-low triangle incidence in two order49 profiles.
The profile census remains explicit; no graph realization is assumed. -/
namespace Erdos85
open SimpleGraph Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sparse overlap bound contradicts the actual graph fifth-trace residue
when minimum incidence has residue one and at most two triple supports. -/
theorem orderFortyNine_lowLow_sum_ne_minimal_of_residue
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hthree : orderFortyNineHighIncidenceCount G 3 ≤ 2)
    (hres : Int.ModEq 5
      ((orderFortyNineHighIncidenceCount G 0 : ℤ) +
        ((orderFortyNineHighVertices G).card : ℤ) + 4) 1) :
    (∑ x ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G x) ≠
      orderFortyNineHighIncidenceCount G 0 := by
  intro hsum
  have hbound := (orderFortyNine_sparse_overlap_of_minimal_sum
    G hfree hmin hcard hsum).2 hthree
  have hcubic := orderFortyNine_cubic_trace_eq_lowLow_sum G hfree hmin hcard
  have hsint : (∑ x ∈ orderFortyNineLowVertices G,
      (orderFortyNineLowLowLocalEdgeCount G x : ℤ)) =
      (orderFortyNineHighIncidenceCount G 0 : ℤ) := by exact_mod_cast hsum
  rw [hsint] at hcubic
  have hmod := orderFortyNine_overlap_residue_of_cubic_incidence G hfree hmin hcard
    (orderFortyNineHighIncidenceCount G 0 : ℤ) hcubic
  have hcyclic : Matrix.trace (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) =
      Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) := by
    rw [Matrix.trace_mul_cycle]
  rw [hcyclic] at hmod
  exact hbound (hmod.trans hres)

/-- The 3-high census with 1 triple supports cannot attain minimum
all-low triangle incidence 24. -/
theorem orderFortyNine_threeHigh_triple_lowLow_sum_ne_24
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hh : (orderFortyNineHighVertices G).card = 3)
    (hzero : orderFortyNineHighIncidenceCount G 0 = 24) :
    (∑ x ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G x) ≠ 24 := by
  have hcensus := orderFortyNine_highIncidence_census G hfree hmin hcard
  rw [hh, hzero] at hcensus
  have hn := orderFortyNine_lowLow_sum_ne_minimal_of_residue G hfree hmin hcard
    (by omega) (by rw [hzero, hh]; decide)
  simpa only [hzero] using hn

/-- The 5-high census with 2 triple supports cannot attain minimum
all-low triangle incidence 12. -/
theorem orderFortyNine_fiveHigh_twoTriple_lowLow_sum_ne_12
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hh : (orderFortyNineHighVertices G).card = 5)
    (hzero : orderFortyNineHighIncidenceCount G 0 = 12) :
    (∑ x ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G x) ≠ 12 := by
  have hcensus := orderFortyNine_highIncidence_census G hfree hmin hcard
  rw [hh, hzero] at hcensus
  have hn := orderFortyNine_lowLow_sum_ne_minimal_of_residue G hfree hmin hcard
    (by omega) (by rw [hzero, hh]; decide)
  simpa only [hzero] using hn

end Erdos85
