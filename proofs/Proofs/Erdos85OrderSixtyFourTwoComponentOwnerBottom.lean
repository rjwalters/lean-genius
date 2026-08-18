import Proofs.Erdos85BinarySquareOwnerBottomMultiplicity

/-! # Exact uncentered owner-bottom multiplicities at order 64

The centered owner kernels contain the constant direction.  This file records
the corresponding exact *uncentered* bottom eigenspaces for the three
two-component strata, removing that extra direction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the `[6,2]` stratum the two owner bottom multiplicities are exactly
`16` and `48`. -/
theorem orderSixtyFour_sixTwo_componentOwner_bottom_multiplicities
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (ha : a.supp.ncard = 48) (hb : b.supp.ncard = 16) :
    Module.finrank ℝ (LinearMap.ker
        ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℝ +
          (6 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ)).mulVecLin) = 16 ∧
      Module.finrank ℝ (LinearMap.ker
        ((componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℝ +
          (2 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ)).mulVecLin) = 48 := by
  constructor
  · simpa using
      (binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
        G hfree (q := 8) (by norm_num) hreg (by norm_num) a
          (m_c := 6) (by simpa using ha))
  · simpa using
      (binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
        G hfree (q := 8) (by norm_num) hreg (by norm_num) b
          (m_c := 2) (by simpa using hb))

/-- In the `[5,3]` stratum the two owner bottom multiplicities are exactly
`24` and `40`. -/
theorem orderSixtyFour_fiveThree_componentOwner_bottom_multiplicities
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (ha : a.supp.ncard = 40) (hb : b.supp.ncard = 24) :
    Module.finrank ℝ (LinearMap.ker
        ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℝ +
          (5 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ)).mulVecLin) = 24 ∧
      Module.finrank ℝ (LinearMap.ker
        ((componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℝ +
          (3 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ)).mulVecLin) = 40 := by
  constructor
  · simpa using
      (binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
        G hfree (q := 8) (by norm_num) hreg (by norm_num) a
          (m_c := 5) (by simpa using ha))
  · simpa using
      (binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
        G hfree (q := 8) (by norm_num) hreg (by norm_num) b
          (m_c := 3) (by simpa using hb))

/-- In the `[4,4]` stratum both owner bottom multiplicities are exactly
`32`. -/
theorem orderSixtyFour_fourFour_componentOwner_bottom_multiplicities
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (ha : a.supp.ncard = 32) (hb : b.supp.ncard = 32) :
    Module.finrank ℝ (LinearMap.ker
        ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℝ +
          (4 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ)).mulVecLin) = 32 ∧
      Module.finrank ℝ (LinearMap.ker
        ((componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℝ +
          (4 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ)).mulVecLin) = 32 := by
  constructor
  · simpa using
      (binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
        G hfree (q := 8) (by norm_num) hreg (by norm_num) a
          (m_c := 4) (by simpa using ha))
  · simpa using
      (binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
        G hfree (q := 8) (by norm_num) hreg (by norm_num) b
          (m_c := 4) (by simpa using hb))

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sixTwo_componentOwner_bottom_multiplicities
#print axioms Erdos85.orderSixtyFour_fiveThree_componentOwner_bottom_multiplicities
#print axioms Erdos85.orderSixtyFour_fourFour_componentOwner_bottom_multiplicities
