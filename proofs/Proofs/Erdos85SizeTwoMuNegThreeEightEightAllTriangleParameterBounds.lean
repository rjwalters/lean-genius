import Proofs.Erdos85SizeTwoMuNegThreeEightEightSharpParameterBounds
import Proofs.Erdos85TriangleFreeSecondOrderIntersection

/-! # All-triangle parameter pressure in the `mu=-3` C8+C8 branch -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- A subset of a four-element set that avoids two distinct specified
elements has cardinality at most two. -/
theorem card_le_two_of_subset_card_four_avoid_two
    {α : Type*} [DecidableEq α] (S T : Finset α) (p q : α)
    (hS : S.card = 4) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    (hsub : T ⊆ S) (hpT : p ∉ T) (hqT : q ∉ T) :
    T.card ≤ 2 := by
  have hins : insert p (insert q T) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hp
    · exact hq
    · exact hsub hx
  have hcard : (insert p (insert q T)).card = T.card + 2 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem hqT]
    · simp [hpT, hpq]
  have := Finset.card_le_card hins
  rw [hcard, hS] at this
  omega

/-- If the two cycle-neighbor entries vanish, an alternating C8 row has at
most two opposite-sign entries. -/
theorem alternating_C8_row_card_le_same_add_two_of_cycleZeros
    (N : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hminus : N 0 (-1) ≠ 1) (hplus : N 0 1 ≠ 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1).card ≤
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f 0 ∧ N 0 j = 1).card + 2 := by
  classical
  let S := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ f j ≠ f 0
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    f j ≠ f 0 ∧ N 0 j = 1
  have hS : S.card = 4 :=
    (zmodEight_alternating_sign_class_cards_four
      f hsign hflip (f 0) (hsign 0)).2
  have hneg (i : ZMod 8) (hi : f i = -f 0) : f i ≠ f 0 := by
    rcases hsign 0 with h0 | h0 <;> omega
  have hp : (-1 : ZMod 8) ∈ S := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hneg _ ?_⟩
    have h := hflip (-1)
    norm_num at h ⊢
    omega
  have hq : (1 : ZMod 8) ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hneg _ (by simpa using hflip 0)⟩
  have hpq : (-1 : ZMod 8) ≠ 1 := by decide
  have hsub : T ⊆ S := by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
  have hpT : (-1 : ZMod 8) ∉ T := by
    intro h
    exact hminus (Finset.mem_filter.mp h).2.2
  have hqT : (1 : ZMod 8) ∉ T := by
    intro h
    exact hplus (Finset.mem_filter.mp h).2.2
  have hTle : T.card ≤ 2 :=
    card_le_two_of_subset_card_four_avoid_two S T (-1) 1
      hS hp hq hpq hsub hpT hqT
  let R := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ f j = f 0) (s := R)
  have hsame : (R.filter fun j ↦ f j = f 0).card =
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f 0 ∧ N 0 j = 1).card := by
    congr 1
    ext j
    simp [R, and_comm]
  have hopp : (R.filter fun j ↦ ¬ f j = f 0).card = T.card := by
    congr 1
    ext j
    simp [R, T, and_comm]
  calc
    R.card = (R.filter fun j ↦ f j = f 0).card +
        (R.filter fun j ↦ ¬ f j = f 0).card := hpart.symm
    _ ≤ (R.filter fun j ↦ f j = f 0).card + 2 :=
      Nat.add_le_add_left (by simpa [hopp] using hTle) _
    _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f 0 ∧ N 0 j = 1).card + 2 := by rw [hsame]

/-- An internal quotient row of size `7-r`, with same-sign degree `k`,
forces `5 ≤ r+k` once its two cycle-neighbor entries vanish. -/
theorem alternating_C8_allTriangle_internal_parameter_lower
    (N : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ) (k r : ℕ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r)
    (hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f 0 ∧ N 0 j = 1).card = k)
    (hminus : N 0 (-1) ≠ 1) (hplus : N 0 1 ≠ 1) :
    5 ≤ r + k := by
  have hle := alternating_C8_row_card_le_same_add_two_of_cycleZeros
    N f hsign hflip hminus hplus
  rw [hNrow, hNsame] at hle
  omega

end

end Erdos85

#print axioms Erdos85.card_le_two_of_subset_card_four_avoid_two
#print axioms Erdos85.alternating_C8_row_card_le_same_add_two_of_cycleZeros
#print axioms Erdos85.alternating_C8_allTriangle_internal_parameter_lower
