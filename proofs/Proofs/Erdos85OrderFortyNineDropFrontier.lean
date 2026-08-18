import Proofs.Erdos85OrderFortyNineVerifiedFrontier
import Proofs.Erdos85FiniteDropWitnesses

/-!
# Order-49 certificate frontier to the checked finite drop

This packages the exact surviving certificate obligations and connects them
directly to the checked order-48/order-49 witnesses.  Thus downstream users
need not manually repeat the fourteen-input stratum assembly before obtaining
the exact threshold values and strict finite drop.
-/

namespace Erdos85

structure OrderFortyNineVerifiedCertificateFrontier : Prop where
  one : ∀ (profile : Fin 5) table,
    table ∈ oneHighCapacityInventoryTables profile →
      OneHighFamilyV2CheckedUnsat profile.val table
  threeZero : OrderFortyNineTripleCellExcluded 3 0
  threeOne : OrderFortyNineTripleCellExcluded 3 1
  fiveZero : OrderFortyNineTripleCellExcluded 5 0
  fiveOne : OrderFortyNineTripleCellExcluded 5 1
  fiveTwo : OrderFortyNineTripleCellExcluded 5 2
  sevenZero : OrderFortyNineTripleCellExcluded 7 0
  sevenOne : OrderFortyNineTripleCellExcluded 7 1
  sevenTwo : OrderFortyNineTripleCellExcluded 7 2
  sevenThree : OrderFortyNineTripleCellExcluded 7 3
  sevenFour : OrderFortyNineTripleCellExcluded 7 4
  sevenFive : OrderFortyNineTripleCellExcluded 7 5
  sevenSix : OrderFortyNineTripleCellExcluded 7 6
  sevenSeven : OrderFortyNineTripleCellExcluded 7 7

theorem OrderFortyNineVerifiedCertificateFrontier.no_degreeSeven_witness
    (h : OrderFortyNineVerifiedCertificateFrontier) :
    ¬ C4FreeMinDegreeWitness 49 7 :=
  not_c4FreeMinDegreeWitness_fortyNine_seven_of_verifiedFrontier
    h.one h.threeZero h.threeOne h.fiveZero h.fiveOne h.fiveTwo
    h.sevenZero h.sevenOne h.sevenTwo h.sevenThree h.sevenFour
    h.sevenFive h.sevenSix h.sevenSeven

theorem OrderFortyNineVerifiedCertificateFrontier.exact_thresholds
    (h : OrderFortyNineVerifiedCertificateFrontier) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 :=
  minDegreeForC4_fortyEight_fortyNine_exact_checked
    h.no_degreeSeven_witness

theorem OrderFortyNineVerifiedCertificateFrontier.strict_drop
    (h : OrderFortyNineVerifiedCertificateFrontier) :
    minDegreeForC4 49 < minDegreeForC4 48 :=
  minDegreeForC4_fortyNine_lt_fortyEight_checked
    h.no_degreeSeven_witness

theorem OrderFortyNineVerifiedCertificateFrontier.ramsey_plateau
    (h : OrderFortyNineVerifiedCertificateFrontier) :
    ConsecutiveC4StarPlateauAt 48 41 :=
  consecutiveC4StarPlateauAt_fortyEight boza48_degreeSeven_witness
    h.no_degreeSeven_witness

end Erdos85
