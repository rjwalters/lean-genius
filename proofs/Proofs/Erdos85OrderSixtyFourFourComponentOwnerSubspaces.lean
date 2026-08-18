import Proofs.Erdos85BinarySquareCenteredOwnerRank
import Proofs.Erdos85BinarySquareOwnerCommonBottomSubmodule
import Proofs.Erdos85OrderSixtyFourRegularPartition

/-!
# Exact owner-sector arrangement in the four-component order-64 branch

The maximal binary partition is `2+2+2+2`.  Each centered owner sector then
has rank fifteen, the four ranks total sixty, and the common shifted-owner
bottom submodule has dimension three.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Complete rank package for the regular four-component order-64 stratum. -/
theorem orderSixtyFour_regular_fourComponent_ownerSubspace_package
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4) :
    ∃ m : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ c, c.supp.ncard = 8 * m c) ∧
      (∑ c, m c = 8) ∧
      (∀ c, m c = 2) ∧
      (∀ c,
        (((8 : ℤ) •
              ((componentOwnerGraph G
                  (secondOrderDefectGraph G) c).adjMatrix ℤ +
                (m c : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ)) -
            (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
              (Int.castRingHom ℝ)).rank = 15) ∧
      (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        (((8 : ℤ) •
              ((componentOwnerGraph G
                  (secondOrderDefectGraph G) c).adjMatrix ℤ +
                (m c : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ)) -
            (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
              (Int.castRingHom ℝ)).rank) = 60 ∧
      Module.finrank ℚ (binarySquareOwnerCommonBottomSubmodule G m) = 3 := by
  classical
  obtain ⟨m, hm, hsum, _hlower, _hcountLe⟩ :=
    orderSixtyFour_regular_defectComponent_partition_package G hfree hreg
  have horders := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hmTwo : ∀ c, m c = 2 := by
    intro c
    have hs := hm c
    rw [horders c] at hs
    omega
  have hrank : ∀ c,
      (((8 : ℤ) •
            ((componentOwnerGraph G
                (secondOrderDefectGraph G) c).adjMatrix ℤ +
              (m c : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ)) -
          (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
            (Int.castRingHom ℝ)).rank = 15 := by
    intro c
    have hcRank := binarySquare_regular_real_centeredOwnerGram_rank
      G hfree (q := 8) (by norm_num) hreg (by norm_num) c (hm c)
    rw [hmTwo c] at hcRank
    rw [hmTwo c]
    norm_num at hcRank ⊢
    exact hcRank
  have hrankSum :
      (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        (((8 : ℤ) •
              ((componentOwnerGraph G
                  (secondOrderDefectGraph G) c).adjMatrix ℤ +
                (m c : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ)) -
            (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
              (Int.castRingHom ℝ)).rank) = 60 := by
    simp_rw [hrank]
    simp [hcount]
  let E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 4 :=
    Fintype.equivFinOfCardEq hcount
  have hcommon : Module.finrank ℚ
      (binarySquareOwnerCommonBottomSubmodule G m) = 3 := by
    rw [binarySquare_regular_finrank_ownerCommonBottomSubmodule
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm hsum (E.symm 0),
      hcount]
  exact ⟨m, hm, hsum, hmTwo, hrank, hrankSum, hcommon⟩

end

end Erdos85
