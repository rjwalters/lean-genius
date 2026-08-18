import Proofs.Erdos85BinarySquareCenteredOwnerSpectrumTransfer

/-! # Exact nullity of every centered owner sector -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Exact centered-owner nullity, q-generic.**  The centered owner sector
attached to a component of order `q m_c` has rank `q m_c - 1`, hence kernel
dimension `q² - (q m_c - 1)`. -/
theorem binarySquare_regular_real_centeredOwnerGram_nullity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    Module.finrank ℝ
      (LinearMap.ker (realCenteredOwnerGram G q m_c c).mulVecLin) =
        q * q - (q * m_c - 1) := by
  let C := realCenteredOwnerGram G q m_c c
  have hrank : C.rank = q * m_c - 1 := by
    simpa only [C, realCenteredOwnerGram] using
      (binarySquare_regular_real_centeredOwnerGram_rank
        G hfree hq hreg hcard c hc)
  have hrankNull := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
  have hdim : Module.finrank ℝ (V → ℝ) = q * q := by
    rw [Module.finrank_fintype_fun_eq_card ℝ, hcard]
  change Module.finrank ℝ (LinearMap.range C.mulVecLin) =
      q * m_c - 1 at hrank
  rw [hrank, hdim] at hrankNull
  change Module.finrank ℝ (LinearMap.ker C.mulVecLin) =
    q * q - (q * m_c - 1)
  omega

/-- Centered-owner nullities in the `[6,2]` order-64 stratum. -/
theorem orderSixtyFour_sixTwo_centeredOwnerNullities
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hma : m a = 6) (hmb : m b = 2) :
    Module.finrank ℝ
        (LinearMap.ker (realCenteredOwnerGram G 8 (m a) a).mulVecLin) = 17 ∧
      Module.finrank ℝ
        (LinearMap.ker (realCenteredOwnerGram G 8 (m b) b).mulVecLin) = 49 := by
  constructor
  · rw [binarySquare_regular_real_centeredOwnerGram_nullity
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a), hma]
  · rw [binarySquare_regular_real_centeredOwnerGram_nullity
      G hfree (q := 8) (by norm_num) hreg (by norm_num) b (hm b), hmb]

/-- Centered-owner nullities in the `[5,3]` order-64 stratum. -/
theorem orderSixtyFour_fiveThree_centeredOwnerNullities
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hma : m a = 5) (hmb : m b = 3) :
    Module.finrank ℝ
        (LinearMap.ker (realCenteredOwnerGram G 8 (m a) a).mulVecLin) = 25 ∧
      Module.finrank ℝ
        (LinearMap.ker (realCenteredOwnerGram G 8 (m b) b).mulVecLin) = 41 := by
  constructor
  · rw [binarySquare_regular_real_centeredOwnerGram_nullity
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a), hma]
  · rw [binarySquare_regular_real_centeredOwnerGram_nullity
      G hfree (q := 8) (by norm_num) hreg (by norm_num) b (hm b), hmb]

/-- Centered-owner nullities in the symmetric `[4,4]` order-64 stratum. -/
theorem orderSixtyFour_fourFour_centeredOwnerNullities
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hma : m a = 4) (hmb : m b = 4) :
    Module.finrank ℝ
        (LinearMap.ker (realCenteredOwnerGram G 8 (m a) a).mulVecLin) = 33 ∧
      Module.finrank ℝ
        (LinearMap.ker (realCenteredOwnerGram G 8 (m b) b).mulVecLin) = 33 := by
  constructor
  · rw [binarySquare_regular_real_centeredOwnerGram_nullity
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a), hma]
  · rw [binarySquare_regular_real_centeredOwnerGram_nullity
      G hfree (q := 8) (by norm_num) hreg (by norm_num) b (hm b), hmb]

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_real_centeredOwnerGram_nullity
#print axioms Erdos85.orderSixtyFour_sixTwo_centeredOwnerNullities
#print axioms Erdos85.orderSixtyFour_fiveThree_centeredOwnerNullities
#print axioms Erdos85.orderSixtyFour_fourFour_centeredOwnerNullities
