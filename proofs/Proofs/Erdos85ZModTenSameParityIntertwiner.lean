import Proofs.Erdos85ZModTenSymmetricTwoSupport

/-!
# Same-parity degree-two self-intertwiners on C10

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

namespace Erdos85

/-- The even residue class in `ZMod 10`, written explicitly for a small
kernel-checked classifier. -/
def ZModTenEvenOffset (z : ZMod 10) : Prop :=
  z = 0 ∨ z = 2 ∨ z = 4 ∨ z = 6 ∨ z = 8

instance (z : ZMod 10) : Decidable (ZModTenEvenOffset z) := by
  unfold ZModTenEvenOffset
  infer_instance

/-- A symmetric binary matrix whose even-difference entries depend only on
the difference and have same-parity row degree two uses exactly offsets
`{±2}` or exactly offsets `{±4}`. -/
theorem zmodTen_sameParity_degreeTwo_offset_dichotomy
    (H : Matrix (ZMod 10) (ZMod 10) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hsymm : ∀ x y, H x y = H y x)
    (hdiff : ∀ {x y x' y' : ZMod 10},
      ZModTenEvenOffset (y - x) → y - x = y' - x' → H x y = H x' y')
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 10)).filter fun y =>
        ZModTenEvenOffset (y - x) ∧ H x y = 1).card = 2) :
    (∀ x y, ZModTenEvenOffset (y - x) →
        (H x y = 1 ↔ y - x = 2 ∨ y - x = 8)) ∨
      (∀ x y, ZModTenEvenOffset (y - x) →
        (H x y = 1 ↔ y - x = 4 ∨ y - x = 6)) := by
  classical
  let f : ZMod 10 → Bool := fun z =>
    decide (ZModTenEvenOffset z ∧ H 0 z = 1)
  have heven_neg (z : ZMod 10) :
      ZModTenEvenOffset (-z) ↔ ZModTenEvenOffset z := by
    revert z
    decide
  have hzero : f 0 = false := by
    simp [f, ZModTenEvenOffset, hdiag]
  have hneg : ∀ z, f (-z) = f z := by
    intro z
    apply Bool.eq_iff_iff.mpr
    simp only [f, decide_eq_true_eq]
    constructor
    · rintro ⟨he, hz⟩
      have he' := (heven_neg z).mp he
      refine ⟨he', ?_⟩
      calc
        H 0 z = H (-z) 0 := by
          apply (hdiff (x := -z) (y := 0) (x' := 0) (y' := z)
            (by simpa using he') ?_).symm
          ring
        _ = H 0 (-z) := hsymm _ _
        _ = 1 := hz
    · rintro ⟨he, hz⟩
      have he' := (heven_neg z).mpr he
      refine ⟨he', ?_⟩
      calc
        H 0 (-z) = H (-z) 0 := hsymm _ _
        _ = H 0 z := by
          apply hdiff (x := -z) (y := 0) (x' := 0) (y' := z)
            (by simpa using he)
          ring
        _ = 1 := hz
  have hcard :
      ((Finset.univ : Finset (ZMod 10)).filter fun z => f z).card = 2 := by
    simpa [f] using hdegree 0
  have heven : ∀ z, f z = true → z = 2 ∨ z = 4 ∨ z = 6 ∨ z = 8 := by
    intro z hz
    have hz' : ZModTenEvenOffset z ∧ H 0 z = 1 := by simpa [f] using hz
    rcases hz'.1 with h0 | h2 | h4 | h6 | h8
    · subst z
      rw [hdiag] at hz'
      omega
    · exact Or.inl h2
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h6))
    · exact Or.inr (Or.inr (Or.inr h8))
  rcases zmodTen_symmetric_even_two_support f hzero hneg hcard heven with hf | hf
  · left
    intro x y he
    have hxy0 : H x y = H 0 (y - x) := by
      apply hdiff he
      ring
    have hf' := hf (y - x)
    simp only [f, decide_eq_true_eq] at hf'
    rw [hxy0]
    simpa [he] using hf'
  · right
    intro x y he
    have hxy0 : H x y = H 0 (y - x) := by
      apply hdiff he
      ring
    have hf' := hf (y - x)
    simp only [f, decide_eq_true_eq] at hf'
    rw [hxy0]
    simpa [he] using hf'

end Erdos85

#print axioms Erdos85.zmodTen_sameParity_degreeTwo_offset_dichotomy
