import Proofs.Erdos85SignedSRGBridge

/-! # Bit-vector and Boolean owner-factor predicates -/

namespace Erdos85

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
  ∀ x y,
    (Finset.univ.filter fun w => f x w && d y w).card =
      (Finset.univ.filter fun w => d x w && f y w).card

def BoolFourFactorization
    (d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool) : Prop :=
  BoolCommutingTwoFactor d f0 ∧ BoolCommutingTwoFactor d f1 ∧
  BoolCommutingTwoFactor d f2 ∧ BoolCommutingTwoFactor d f3 ∧
  ∀ x y, x ≠ y →
    if d x y then
      f0 x y = false ∧ f1 x y = false ∧
      f2 x y = false ∧ f3 x y = false
    else
      (f0 x y = true ∧ f1 x y = false ∧
        f2 x y = false ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = true ∧
        f2 x y = false ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = false ∧
        f2 x y = true ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = false ∧
        f2 x y = false ∧ f3 x y = true)

theorem isCommutingTwoFactor_matrixBV
    {d f : Fin 16 → Fin 16 → Bool}
    (h : BoolCommutingTwoFactor d f) :
    isCommutingTwoFactor (matrixBV d) (matrixBV f) := by
  rcases h with ⟨hloop, hsym, hdeg, hdisj, hcomm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [bitAdj_matrixBV] using hloop x
  · intro x y
    simpa only [bitAdj_matrixBV] using hsym x y
  · intro x
    apply BitVec.eq_of_toNat_eq
    rw [cpop16_eq_filter_card]
    simp only [row256_matrixBV_getLsbD]
    simpa using hdeg x
  · intro x y hxy
    simpa only [bitAdj_matrixBV] using hdisj x y (by
      simpa only [bitAdj_matrixBV] using hxy)
  · intro x y
    apply BitVec.eq_of_toNat_eq
    rw [cpop16_eq_filter_card, cpop16_eq_filter_card]
    simp only [BitVec.getLsbD_and, row256_matrixBV_getLsbD]
    exact hcomm x y

theorem isFourFactorization_matrixBV
    {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    (h : BoolFourFactorization d f0 f1 f2 f3) :
    isFourFactorization (matrixBV d) (matrixBV f0) (matrixBV f1)
      (matrixBV f2) (matrixBV f3) := by
  rcases h with ⟨h0, h1, h2, h3, hresolve⟩
  refine ⟨isCommutingTwoFactor_matrixBV h0,
    isCommutingTwoFactor_matrixBV h1,
    isCommutingTwoFactor_matrixBV h2,
    isCommutingTwoFactor_matrixBV h3, ?_⟩
  intro x y hxy
  simpa only [bitAdj_matrixBV] using hresolve x y hxy

/-- Uniqueness of a commuting two-factor contradicts an exact four-factor
resolution: the first two factors coincide, while every complement edge has
exactly one color. -/
theorem no_fourFactorization_of_unique
    (d h : BitVec 256)
    (hunique : ∀ f, isCommutingTwoFactor d f → f = h) :
    ∀ f0 f1 f2 f3, ¬ isFourFactorization d f0 f1 f2 f3 := by
  intro f0 f1 f2 f3 hfour
  rcases hfour with ⟨hf0, hf1, hf2, hf3, hresolve⟩
  have heq : f1 = f0 := (hunique f1 hf1).trans (hunique f0 hf0).symm
  have hcard :
      (Finset.univ.filter fun y : Fin 16 => bitAdj256 f0 0 y).card = 2 := by
    have hpop := hf0.2.2.1 0
    have hnat := congrArg BitVec.toNat hpop
    rw [cpop16_eq_filter_card] at hnat
    simp only [row256_getLsbD] at hnat
    simpa [BitVec.toNat_ofNat] using hnat
  have hpos : 0 <
      (Finset.univ.filter fun y : Fin 16 => bitAdj256 f0 0 y).card := by
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  have hbit0 : bitAdj256 f0 0 y = true := by simpa using hy
  have hne : (0 : Fin 16) ≠ y := by
    intro h
    subst y
    exact Bool.false_ne_true (hf0.1 0 ▸ hbit0)
  have hres := hresolve 0 y hne
  split at hres
  · exact Bool.false_ne_true (hres.1.symm.trans hbit0)
  · rcases hres with hres | hres | hres | hres
    · rw [heq] at hres
      exact Bool.false_ne_true (hres.2.1.symm.trans hbit0)
    · exact Bool.false_ne_true (hres.1.symm.trans hbit0)
    · exact Bool.false_ne_true (hres.1.symm.trans hbit0)
    · exact Bool.false_ne_true (hres.1.symm.trans hbit0)

end Erdos85
