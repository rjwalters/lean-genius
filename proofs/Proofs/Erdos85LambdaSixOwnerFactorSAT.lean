import Proofs.Erdos85LambdaSixOwnerFactorRelation

/-! # Finite owner-factor obstruction for the four lambda-six representatives -/

namespace Erdos85

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def lambdaSixTenSixT40 : BitVec 256 :=
  0x4555a2aa51552aaa15558aaa546ca836541baa0d5706a98356c1ab6055b0a8d8

def lambdaSixTenSixT30 : BitVec 256 :=
  0x4555a2aa51552aaa15558aaa5529aa94554aa8a55652a9295694a94a54a5aa52

def lambdaSixFiveFiveThreeThreeT40 : BitVec 256 :=
  0x0c1f141f181f63e0a3e0c3e01d231e911d581cac1e46e189e0d4e06ae225e312

def lambdaSixFiveFiveThreeThreeT30 : BitVec 256 :=
  0x0c1f141f181f63e0a3e0c3e01d251e921d491cb41e4ae149e0b4e24ae125e292

theorem no_fourFactorization_tenSixT40 :
    ∀ f0 f1 f2 f3 : BitVec 256,
      ¬ isFourFactorization lambdaSixTenSixT40 f0 f1 f2 f3 := by
  simp only [isFourFactorization, isCommutingTwoFactor, bitAdj256, row256,
    lambdaSixTenSixT40]
  simp (config := { maxSteps := 100000000 }) [Fin.forall_fin_succ]
  bv_decide (config := { timeout := 600 })

theorem no_fourFactorization_tenSixT30 :
    ∀ f0 f1 f2 f3 : BitVec 256,
      ¬ isFourFactorization lambdaSixTenSixT30 f0 f1 f2 f3 := by
  simp only [isFourFactorization, isCommutingTwoFactor, bitAdj256, row256,
    lambdaSixTenSixT30]
  simp (config := { maxSteps := 100000000 }) [Fin.forall_fin_succ]
  bv_decide (config := { timeout := 600 })

theorem no_fourFactorization_fiveFiveThreeThreeT40 :
    ∀ f0 f1 f2 f3 : BitVec 256,
      ¬ isFourFactorization lambdaSixFiveFiveThreeThreeT40 f0 f1 f2 f3 := by
  simp only [isFourFactorization, isCommutingTwoFactor, bitAdj256, row256,
    lambdaSixFiveFiveThreeThreeT40]
  simp (config := { maxSteps := 100000000 }) [Fin.forall_fin_succ]
  bv_decide (config := { timeout := 600 })

theorem no_fourFactorization_fiveFiveThreeThreeT30 :
    ∀ f0 f1 f2 f3 : BitVec 256,
      ¬ isFourFactorization lambdaSixFiveFiveThreeThreeT30 f0 f1 f2 f3 := by
  simp only [isFourFactorization, isCommutingTwoFactor, bitAdj256, row256,
    lambdaSixFiveFiveThreeThreeT30]
  simp (config := { maxSteps := 100000000 }) [Fin.forall_fin_succ]
  bv_decide (config := { timeout := 600 })

end Erdos85
