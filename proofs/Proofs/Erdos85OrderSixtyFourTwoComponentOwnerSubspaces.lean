import Proofs.Erdos85BinarySquareCenteredOwnerSpectrumTransfer
import Proofs.Erdos85BinarySquareOwnerCommonBottomSubmodule
import Proofs.Erdos85OrderSixtyFourRegularPartition

/-! # Exact owner-sector arrangement in the two-component order-64 strata -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Uniform rank package for every regular two-component order-64 stratum.
The exact individual ranks sum arithmetically to 62, while the common
shifted-owner bottom is the remaining one-dimensional nonconstant direction. -/
theorem orderSixtyFour_regular_twoComponent_ownerSubspace_package
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2) :
    ∃ m : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ c, c.supp.ncard = 8 * m c) ∧
      (∑ c, m c = 8) ∧
      (∀ c, (realCenteredOwnerGram G 8 (m c) c).rank = 8 * m c - 1) ∧
      Module.finrank ℚ (binarySquareOwnerCommonBottomSubmodule G m) = 1 := by
  classical
  obtain ⟨m, hm, hsum, _hlower, _hcountLe⟩ :=
    orderSixtyFour_regular_defectComponent_partition_package G hfree hreg
  have hrank : ∀ c,
      (realCenteredOwnerGram G 8 (m c) c).rank = 8 * m c - 1 := by
    intro c
    simpa only [realCenteredOwnerGram] using
      (binarySquare_regular_real_centeredOwnerGram_rank
        G hfree (q := 8) (by norm_num) hreg (by norm_num) c (hm c))
  let E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcount
  have hcommon : Module.finrank ℚ
      (binarySquareOwnerCommonBottomSubmodule G m) = 1 := by
    rw [binarySquare_regular_finrank_ownerCommonBottomSubmodule
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm hsum (E.symm 0),
      hcount]
  exact ⟨m, hm, hsum, hrank, hcommon⟩

/-- Numerical centered-owner rank split in the `[6,2]` stratum. -/
theorem orderSixtyFour_sixTwo_centeredOwnerRanks
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
    (realCenteredOwnerGram G 8 (m a) a).rank = 47 ∧
      (realCenteredOwnerGram G 8 (m b) b).rank = 15 := by
  constructor
  · have hr := binarySquare_regular_real_centeredOwnerGram_rank
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a)
    change (realCenteredOwnerGram G 8 (m a) a).rank = 8 * m a - 1 at hr
    omega
  · have hr := binarySquare_regular_real_centeredOwnerGram_rank
      G hfree (q := 8) (by norm_num) hreg (by norm_num) b (hm b)
    change (realCenteredOwnerGram G 8 (m b) b).rank = 8 * m b - 1 at hr
    omega

/-- Numerical centered-owner rank split in the `[5,3]` stratum. -/
theorem orderSixtyFour_fiveThree_centeredOwnerRanks
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
    (realCenteredOwnerGram G 8 (m a) a).rank = 39 ∧
      (realCenteredOwnerGram G 8 (m b) b).rank = 23 := by
  constructor
  · have hr := binarySquare_regular_real_centeredOwnerGram_rank
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a)
    change (realCenteredOwnerGram G 8 (m a) a).rank = 8 * m a - 1 at hr
    omega
  · have hr := binarySquare_regular_real_centeredOwnerGram_rank
      G hfree (q := 8) (by norm_num) hreg (by norm_num) b (hm b)
    change (realCenteredOwnerGram G 8 (m b) b).rank = 8 * m b - 1 at hr
    omega

/-- Numerical centered-owner rank split in the symmetric `[4,4]` stratum. -/
theorem orderSixtyFour_fourFour_centeredOwnerRanks
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
    (realCenteredOwnerGram G 8 (m a) a).rank = 31 ∧
      (realCenteredOwnerGram G 8 (m b) b).rank = 31 := by
  constructor
  · have hr := binarySquare_regular_real_centeredOwnerGram_rank
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a)
    change (realCenteredOwnerGram G 8 (m a) a).rank = 8 * m a - 1 at hr
    omega
  · have hr := binarySquare_regular_real_centeredOwnerGram_rank
      G hfree (q := 8) (by norm_num) hreg (by norm_num) b (hm b)
    change (realCenteredOwnerGram G 8 (m b) b).rank = 8 * m b - 1 at hr
    omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_twoComponent_ownerSubspace_package
#print axioms Erdos85.orderSixtyFour_sixTwo_centeredOwnerRanks
#print axioms Erdos85.orderSixtyFour_fiveThree_centeredOwnerRanks
#print axioms Erdos85.orderSixtyFour_fourFour_centeredOwnerRanks
