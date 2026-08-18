import Proofs.Erdos85BinarySquareCenteredOwnerCubicTrace
import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger

/-!
# Triangle divisibility from the centered-owner cubic resolution

This turns the q-generic cubic trace divisibility into an actual graph-count
statement: `q²` divides six times the combined number of defect triangles and
owner-color triangles.  Unlike the order-64 record census, the statement is
uniform in `q`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **q-generic combined triangle divisibility.** -/
theorem binarySquare_regular_sq_dvd_six_mul_sum_owner_defect_triangleMinorCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q) :
    (q : ℤ) ^ 2 ∣ 6 *
      (((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card : ℤ) +
        ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
          ((adjacencyTriangleMinorFinset
            (componentOwnerGraph G (secondOrderDefectGraph G) c)).card : ℤ)) := by
  have hV3 : 3 ≤ Fintype.card V := by rw [hcard]; nlinarith
  have hdvd := binarySquare_regular_sq_dvd_sum_owner_defect_cube_traces
    G hfree hq hreg hcard m hm hsum
  rw [trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
    (secondOrderDefectGraph G) hV3] at hdvd
  simp_rw [trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
    _ hV3] at hdvd
  have heq :
      (6 : ℤ) *
          (((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card : ℤ) +
            ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
              ((adjacencyTriangleMinorFinset
                (componentOwnerGraph G (secondOrderDefectGraph G) c)).card : ℤ)) =
        6 * ((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card : ℤ) +
          ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
            6 * ((adjacencyTriangleMinorFinset
              (componentOwnerGraph G (secondOrderDefectGraph G) c)).card : ℤ) := by
    rw [mul_add, Finset.mul_sum]
  rw [heq]
  exact hdvd

/-- At order 64, cancellation of the sole factor two in `6` shows that the
combined triangle count itself is divisible by `32`.  This uses no component
partition census. -/
theorem orderSixtyFour_regular_thirtyTwo_dvd_sum_owner_defect_triangleMinorCounts
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8) :
    (32 : ℤ) ∣
      ((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card : ℤ) +
        ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
          ((adjacencyTriangleMinorFinset
            (componentOwnerGraph G (secondOrderDefectGraph G) c)).card : ℤ) := by
  let T : ℤ :=
    ((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card : ℤ) +
      ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        ((adjacencyTriangleMinorFinset
          (componentOwnerGraph G (secondOrderDefectGraph G) c)).card : ℤ)
  have hdvd : (64 : ℤ) ∣ 6 * T := by
    simpa [T] using
      (binarySquare_regular_sq_dvd_six_mul_sum_owner_defect_triangleMinorCounts
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm hsum)
  obtain ⟨z, hz⟩ := hdvd
  have h32 : (32 : ℤ) ∣ 3 * T := by
    refine ⟨z, ?_⟩
    ring_nf at hz ⊢
    nlinarith
  have hcop : IsCoprime (32 : ℤ) 3 := by norm_num
  exact hcop.dvd_of_dvd_mul_left h32

end

end Erdos85

#print axioms
  Erdos85.binarySquare_regular_sq_dvd_six_mul_sum_owner_defect_triangleMinorCounts
#print axioms
  Erdos85.orderSixtyFour_regular_thirtyTwo_dvd_sum_owner_defect_triangleMinorCounts
