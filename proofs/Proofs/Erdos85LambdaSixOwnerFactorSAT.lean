import Proofs.Erdos85SignedSRGBridge

/-! # Finite owner-factor obstruction for the four lambda-six representatives -/

namespace Erdos85

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def isCommutingTwoFactor (d f : BitVec 256) : Prop :=
  (∀ x : Fin 16, bitAdj256 f x x = false) ∧
  (∀ x y : Fin 16, bitAdj256 f x y = bitAdj256 f y x) ∧
  (∀ x : Fin 16, (row256 f x).cpop = 2) ∧
  (∀ x y : Fin 16, bitAdj256 f x y = true → bitAdj256 d x y = false) ∧
  (∀ x y : Fin 16,
    ((row256 f x) &&& (row256 d y)).cpop =
      ((row256 d x) &&& (row256 f y)).cpop)

def isFourFactorization
    (d f0 f1 f2 f3 : BitVec 256) : Prop :=
  isCommutingTwoFactor d f0 ∧ isCommutingTwoFactor d f1 ∧
  isCommutingTwoFactor d f2 ∧ isCommutingTwoFactor d f3 ∧
  ∀ x y : Fin 16, x ≠ y →
    if bitAdj256 d x y then
      bitAdj256 f0 x y = false ∧ bitAdj256 f1 x y = false ∧
      bitAdj256 f2 x y = false ∧ bitAdj256 f3 x y = false
    else
      (bitAdj256 f0 x y = true ∧ bitAdj256 f1 x y = false ∧
        bitAdj256 f2 x y = false ∧ bitAdj256 f3 x y = false) ∨
      (bitAdj256 f0 x y = false ∧ bitAdj256 f1 x y = true ∧
        bitAdj256 f2 x y = false ∧ bitAdj256 f3 x y = false) ∨
      (bitAdj256 f0 x y = false ∧ bitAdj256 f1 x y = false ∧
        bitAdj256 f2 x y = true ∧ bitAdj256 f3 x y = false) ∨
      (bitAdj256 f0 x y = false ∧ bitAdj256 f1 x y = false ∧
        bitAdj256 f2 x y = false ∧ bitAdj256 f3 x y = true)

def BoolCommutingTwoFactor
    (d f : Fin 16 → Fin 16 → Bool) : Prop :=
  (∀ x, f x x = false) ∧
  (∀ x y, f x y = f y x) ∧
  (∀ x, (Finset.univ.filter fun y => f x y).card = 2) ∧
  (∀ x y, f x y = true → d x y = false) ∧
  (∀ x y,
    (Finset.univ.filter fun z => f x z && d y z).card =
      (Finset.univ.filter fun z => d x z && f y z).card)

def BoolFourFactorization
    (d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool) : Prop :=
  BoolCommutingTwoFactor d f0 ∧ BoolCommutingTwoFactor d f1 ∧
  BoolCommutingTwoFactor d f2 ∧ BoolCommutingTwoFactor d f3 ∧
  ∀ x y, x ≠ y →
    if d x y then
      f0 x y = false ∧ f1 x y = false ∧
      f2 x y = false ∧ f3 x y = false
    else
      (f0 x y = true ∧ f1 x y = false ∧ f2 x y = false ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = true ∧ f2 x y = false ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = false ∧ f2 x y = true ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = false ∧ f2 x y = false ∧ f3 x y = true)

theorem isFourFactorization_matrixBV
    {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    (h : BoolFourFactorization d f0 f1 f2 f3) :
    isFourFactorization (matrixBV d) (matrixBV f0) (matrixBV f1)
      (matrixBV f2) (matrixBV f3) := by
  have packageFactor : ∀ {f}, BoolCommutingTwoFactor d f →
      isCommutingTwoFactor (matrixBV d) (matrixBV f) := by
    intro f hf
    rcases hf with ⟨hloop, hsym, hdeg, hsub, hcomm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [bitAdj_matrixBV] using hloop
    · simpa only [bitAdj_matrixBV] using hsym
    · intro x
      apply BitVec.eq_of_toNat_eq
      rw [cpop16_eq_filter_card]
      simp only [row256_matrixBV_getLsbD]
      simpa using hdeg x
    · simpa only [bitAdj_matrixBV] using hsub
    · intro x y
      apply BitVec.eq_of_toNat_eq
      rw [cpop16_eq_filter_card, cpop16_eq_filter_card]
      simp only [BitVec.getLsbD_and, row256_matrixBV_getLsbD]
      simpa using hcomm x y
  rcases h with ⟨h0, h1, h2, h3, hpartition⟩
  refine ⟨packageFactor h0, packageFactor h1, packageFactor h2,
    packageFactor h3, ?_⟩
  intro x y hxy
  simpa only [bitAdj_matrixBV] using hpartition x y hxy

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
