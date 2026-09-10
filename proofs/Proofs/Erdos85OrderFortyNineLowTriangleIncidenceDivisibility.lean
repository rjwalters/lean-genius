import Proofs.Erdos85OrderFortyNineCubicLowTriangleTrace
import Proofs.Erdos85OrderFortyNineMinimalTriangleExclusion

/-! Divisibility of the existing all-low local incidence sum. No new global
triangle-object representation is introduced. -/
namespace Erdos85
open Matrix Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Frobenius gives cubic trace divisibility for any trace-zero integer matrix. -/
theorem three_dvd_trace_cube_of_trace_zero (A : Matrix V V ℤ)
    (htrace : Matrix.trace A = 0) : (3 : ℤ) ∣ Matrix.trace (A ^ 3) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let f := Int.castRingHom (ZMod 3)
  let B : Matrix V V (ZMod 3) := A.map f
  have hmap (n : ℕ) : ((Matrix.trace (A ^ n) : ℤ) : ZMod 3) =
      Matrix.trace (B ^ n) := by
    rw [Matrix.trace, Matrix.trace]
    push_cast
    change (∑ x, f ((A ^ n) x x)) = ∑ x, ((A.map f) ^ n) x x
    rw [← Matrix.map_pow]
    rfl
  have hf := ZMod.trace_pow_card (p := 3) B
  have hb : Matrix.trace B = 0 := by
    simpa [htrace] using (hmap 1).symm
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  rw [hmap 3, hf, hb]
  norm_num

/-- The actual low-triangle incidence sum is a multiple of3. -/
theorem orderFortyNine_three_dvd_lowLow_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49) :
    3 ∣ ∑ v ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G v := by
  have hc := orderFortyNine_cubic_trace_eq_lowLow_sum G hfree hmin hcard
  obtain ⟨k, hk⟩ := three_dvd_trace_cube_of_trace_zero (G.adjMatrix ℤ)
    (SimpleGraph.trace_adjMatrix ℤ G)
  rw [hc] at hk
  have hi : (3 : ℤ) ∣ ∑ v ∈ orderFortyNineLowVertices G,
      (orderFortyNineLowLowLocalEdgeCount G v : ℤ) := by
    omega
  exact_mod_cast hi

/-- Empty supports give a lower bound on total low-triangle incidence. -/
theorem orderFortyNine_empty_count_le_lowLow_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49) :
    orderFortyNineHighIncidenceCount G 0 ≤
      ∑ v ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G v := by
  classical
  have hpoint : ∀ v ∈ orderFortyNineLowVertices G,
      (if (G.neighborFinset v ∩ orderFortyNineHighVertices G).card = 0 then 1 else 0) ≤
        orderFortyNineLowLowLocalEdgeCount G v := by
    intro v hv
    have hlow : G.degree v = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard v with h | h
      · exact h
      · exact ((Finset.mem_sdiff.mp hv).2 (by simp [orderFortyNineHighVertices, h])).elim
    split_ifs with hz
    · exact orderFortyNine_lowLowLocalEdgeCount_pos_of_no_high G hfree hmin hcard hlow hz
    · omega
  have hsum := Finset.sum_le_sum hpoint
  simpa [orderFortyNineHighIncidenceCount] using hsum
/-- The H3 triple-support profile has at least27 all-low incidences. -/
theorem orderFortyNine_threeHigh_lowLow_sum_ge_twentySeven
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49)
    (hh : (orderFortyNineHighVertices G).card = 3)
    (hzero : orderFortyNineHighIncidenceCount G 0 = 24) :
    27 ≤ ∑ v ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G v := by
  have hd := orderFortyNine_three_dvd_lowLow_sum G hfree hmin hcard
  have hb := orderFortyNine_empty_count_le_lowLow_sum G hfree hmin hcard
  rw [hzero] at hb
  have hn := orderFortyNine_threeHigh_triple_lowLow_sum_ne_24 G hfree hmin hcard hh hzero
  omega

/-- The H5 two-triple-support profile has at least15 all-low incidences. -/
theorem orderFortyNine_fiveHigh_lowLow_sum_ge_fifteen
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49)
    (hh : (orderFortyNineHighVertices G).card = 5)
    (hzero : orderFortyNineHighIncidenceCount G 0 = 12) :
    15 ≤ ∑ v ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G v := by
  have hd := orderFortyNine_three_dvd_lowLow_sum G hfree hmin hcard
  have hb := orderFortyNine_empty_count_le_lowLow_sum G hfree hmin hcard
  rw [hzero] at hb
  have hn := orderFortyNine_fiveHigh_twoTriple_lowLow_sum_ne_12 G hfree hmin hcard hh hzero
  omega
end Erdos85
