import Proofs.Erdos85EvenCycleOrientation

/-!
# Same-parity degree-one self-intertwiners on C8

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The unique same-parity neighbour in a symmetric C8 self-intertwiner must be
the half-turn.  This is the finite coordinate endpoint for the high `8+8`
diagonal defect matching.
-/

namespace Erdos85

set_option maxRecDepth 100000

/-- The even residue class in `ZMod 8`. -/
def ZModEightEvenOffset (z : ZMod 8) : Prop :=
  z = 0 ∨ z = 2 ∨ z = 4 ∨ z = 6

instance (z : ZMod 8) : Decidable (ZModEightEvenOffset z) := by
  unfold ZModEightEvenOffset
  infer_instance

/-- A negation-invariant singleton support on the nonzero even offsets of
`ZMod 8` consists of the half-turn `4`. -/
theorem zmodEight_symmetric_even_single_support
    (f : ZMod 8 → Bool)
    (hzero : f 0 = false)
    (hneg : ∀ z, f (-z) = f z)
    (hcard : ((Finset.univ : Finset (ZMod 8)).filter fun z => f z).card = 1)
    (heven : ∀ z, f z = true → z = 2 ∨ z = 4 ∨ z = 6) :
    ∀ z, f z = true ↔ z = 4 := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hfa : f a = true := by
    have : a ∈ (Finset.univ : Finset (ZMod 8)).filter fun z => f z := by
      rw [ha]
      simp
    simpa using (Finset.mem_filter.mp this).2
  have ha4 : a = 4 := by
    rcases heven a hfa with ha2 | ha4 | ha6
    · subst a
      have hf6 : f 6 = true := by
        have hn := hneg 2
        exact hn.trans hfa
      have hm6 : (6 : ZMod 8) ∈
          (Finset.univ : Finset (ZMod 8)).filter fun z => f z := by simp [hf6]
      rw [ha] at hm6
      norm_num at hm6
      exact False.elim ((by decide : (6 : ZMod 8) ≠ 2) hm6)
    · exact ha4
    · subst a
      have hf2 : f 2 = true := by
        have hn := hneg 6
        exact hn.trans hfa
      have hm2 : (2 : ZMod 8) ∈
          (Finset.univ : Finset (ZMod 8)).filter fun z => f z := by simp [hf2]
      rw [ha] at hm2
      norm_num at hm2
      exact False.elim ((by decide : (2 : ZMod 8) ≠ 6) hm2)
  intro z
  constructor
  · intro hfz
    have hm : z ∈ (Finset.univ : Finset (ZMod 8)).filter fun w => f w := by
      simp [hfz]
    rw [ha] at hm
    simpa [ha4] using hm
  · intro hz
    simpa [hz, ha4] using hfa

/-- A symmetric matrix whose even-difference entries depend only on the
difference and whose same-parity row degree is one uses exactly offset `4`. -/
theorem zmodEight_sameParity_degreeOne_offset_four
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hsymm : ∀ x y, H x y = H y x)
    (hdiff : ∀ {x y x' y' : ZMod 8},
      ZModEightEvenOffset (y - x) → y - x = y' - x' → H x y = H x' y')
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ZModEightEvenOffset (y - x) ∧ H x y = 1).card = 1) :
    ∀ x y, ZModEightEvenOffset (y - x) →
      (H x y = 1 ↔ y - x = 4) := by
  classical
  let f : ZMod 8 → Bool := fun z =>
    decide (ZModEightEvenOffset z ∧ H 0 z = 1)
  have heven_neg (z : ZMod 8) :
      ZModEightEvenOffset (-z) ↔ ZModEightEvenOffset z := by
    revert z
    decide
  have hzero : f 0 = false := by
    simp [f, ZModEightEvenOffset, hdiag]
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
      ((Finset.univ : Finset (ZMod 8)).filter fun z => f z).card = 1 := by
    simpa [f] using hdegree 0
  have heven : ∀ z, f z = true → z = 2 ∨ z = 4 ∨ z = 6 := by
    intro z hz
    have hz' : ZModEightEvenOffset z ∧ H 0 z = 1 := by simpa [f] using hz
    rcases hz'.1 with h0 | h2 | h4 | h6
    · subst z
      rw [hdiag] at hz'
      omega
    · exact Or.inl h2
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr h6)
  have hf := zmodEight_symmetric_even_single_support f hzero hneg hcard heven
  intro x y he
  have hxy0 : H x y = H 0 (y - x) := by
    apply hdiff he
    ring
  have hf' := hf (y - x)
  simp only [f, decide_eq_true_eq] at hf'
  rw [hxy0]
  simpa [he] using hf'

/-- Recurrence-ready form: looplessness and the C8 self-intertwining
equation supply the required even-difference translation invariance. -/
theorem zmodEight_selfIntertwiner_sameParity_degreeOne_offset_four
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hsymm : ∀ x y, H x y = H y x)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ZModEightEvenOffset (y - x) ∧ H x y = 1).card = 1) :
    ∀ x y, ZModEightEvenOffset (y - x) →
      (H x y = 1 ↔ y - x = 4) := by
  apply zmodEight_sameParity_degreeOne_offset_four H hdiag hsymm
  · intro x y x' y' he hsub
    apply selfIntertwiner_eq_of_sub_eq_of_mem_range_two H hdiag hinter ?_ hsub
    rcases he with h0 | h2 | h4 | h6
    · refine ⟨0, ?_⟩
      change 2 * (0 : ZMod 8) = y - x
      rw [h0]
      norm_num
    · refine ⟨1, ?_⟩
      change 2 * (1 : ZMod 8) = y - x
      rw [h2]
      norm_num
    · refine ⟨2, ?_⟩
      change 2 * (2 : ZMod 8) = y - x
      rw [h4]
      decide
    · refine ⟨3, ?_⟩
      change 2 * (3 : ZMod 8) = y - x
      rw [h6]
      decide
  · exact hdegree

end Erdos85

#print axioms Erdos85.zmodEight_symmetric_even_single_support
#print axioms Erdos85.zmodEight_sameParity_degreeOne_offset_four
#print axioms Erdos85.zmodEight_selfIntertwiner_sameParity_degreeOne_offset_four
