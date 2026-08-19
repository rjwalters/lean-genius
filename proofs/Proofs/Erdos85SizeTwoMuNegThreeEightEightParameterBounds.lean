import Proofs.Erdos85SizeTwoMuNegThreeEightEightCrossSameMatching

/-! # Signed capacity bounds for the `mu=-3` C8+C8 quotient -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- Every sign class, and its complement, has cardinality four on an
alternating signed C8. -/
theorem zmodEight_alternating_sign_class_cards_four
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (t : ℤ) (ht : t = -1 ∨ t = 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ f i = t).card = 4 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ f i ≠ t).card = 4 := by
  classical
  obtain ⟨hsame, hopp⟩ := zmodEight_alternating_sign_filter_cards
    f hsign hflip
  have htcard : ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      f i = t).card = 4 := by
    rcases ht with rfl | rfl <;> rcases hsign 0 with h0 | h0
    · simpa [h0] using hsame
    · simpa [h0] using hopp
    · simpa [h0] using hopp
    · simpa [h0] using hsame
  constructor
  · exact htcard
  · have hpart := Finset.card_filter_add_card_filter_not
      (fun i : ZMod 8 ↦ f i = t) (s := Finset.univ)
    rw [htcard, show (Finset.univ : Finset (ZMod 8)).card = 8 by decide] at hpart
    have hn : ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        ¬ f i = t).card = 4 := by omega
    simpa only [ne_eq] using hn

/-- A binary row on an alternating C8 has at most four entries outside any
fixed sign class. -/
theorem binary_C8_row_card_le_same_add_four
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (x : ZMod 8) (t : ℤ) (ht : t = -1 ∨ t = 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M x j = 1).card ≤
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = t ∧ M x j = 1).card + 4 := by
  classical
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ M x j = 1
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ f j = t) (s := T)
  have hoppSub : (T.filter fun j ↦ ¬ f j = t) ⊆
      (Finset.univ : Finset (ZMod 8)).filter fun j ↦ f j ≠ t := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.2⟩
  have hoppLe : (T.filter fun j ↦ ¬ f j = t).card ≤ 4 := by
    calc
      _ ≤ ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ f j ≠ t).card :=
        Finset.card_le_card hoppSub
      _ = 4 := (zmodEight_alternating_sign_class_cards_four
        f hsign hflip t ht).2
  have hsameEq : (T.filter fun j ↦ f j = t).card =
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = t ∧ M x j = 1).card := by
    congr 1
    ext j
    simp [T, and_comm]
  have hle : T.card ≤
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = t ∧ M x j = 1).card + 4 := by
    calc
      T.card = (T.filter fun j ↦ f j = t).card +
          (T.filter fun j ↦ ¬ f j = t).card := hpart.symm
      _ ≤ (T.filter fun j ↦ f j = t).card + 4 :=
        Nat.add_le_add_left hoppLe _
      _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          f j = t ∧ M x j = 1).card + 4 := by rw [hsameEq]
  simpa [T] using hle

/-- The internal and cross signed row counts force the sharp arithmetic
window `3 ≤ r+k ≤ 6`.  Thus `k=0` implies `r≥3`, `k=1` implies
`r≤5`, and `k=2` implies `r≤4`. -/
theorem alternating_C8_internal_cross_parameter_bounds
    (N M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (k r : ℕ) (hk : k ≤ 2)
    (hfsign : ∀ i, f i = -1 ∨ f i = 1)
    (hgsign : ∀ i, g i = -1 ∨ g i = 1)
    (hfflip : ∀ i, f (i + 1) = -f i)
    (hgflip : ∀ i, g (i + 1) = -g i)
    (hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r)
    (hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f 0 ∧ N 0 j = 1).card = k)
    (hMrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      M 0 j = 1).card = r)
    (hMsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f 0 ∧ M 0 j = 1).card = 2 - k) :
    3 ≤ r + k ∧ r + k ≤ 6 ∧
      (k = 0 → 3 ≤ r) ∧
      (k = 1 → r ≤ 5) ∧
      (k = 2 → r ≤ 4) := by
  have hNle := binary_C8_row_card_le_same_add_four
    N f hfsign hfflip 0 (f 0) (hfsign 0)
  have hMle := binary_C8_row_card_le_same_add_four
    M g hgsign hgflip 0 (f 0) (hfsign 0)
  rw [hNrow, hNsame] at hNle
  rw [hMrow, hMsame] at hMle
  omega

end

end Erdos85

#print axioms Erdos85.alternating_C8_internal_cross_parameter_bounds
