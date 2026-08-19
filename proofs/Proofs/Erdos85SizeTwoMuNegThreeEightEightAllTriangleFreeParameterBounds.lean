import Proofs.Erdos85SizeTwoMuNegThreeEightEightAllTriangleParameterBounds

/-! # All-triangle-free parameter pressure in the `mu=-3` C8+C8 branch -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- If both cycle-neighbor entries occur in an alternating C8 row, they add
two entries disjoint from its same-sign support. -/
theorem alternating_C8_row_same_add_two_le_of_cycleOnes
    (N : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hminus : N 0 (-1) = 1) (hplus : N 0 1 = 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f 0 ∧ N 0 j = 1).card + 2 ≤
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1).card := by
  classical
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    f j = f 0 ∧ N 0 j = 1
  let R := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1
  have hneg (i : ZMod 8) (hi : f i = -f 0) : f i ≠ f 0 := by
    rcases hsign 0 with h0 | h0 <;> omega
  have hpT : (-1 : ZMod 8) ∉ T := by
    intro h
    have hs := (Finset.mem_filter.mp h).2.1
    have hf : f (-1) = -f 0 := by
      have h := hflip (-1)
      norm_num at h ⊢
      omega
    exact hneg _ hf hs
  have hqT : (1 : ZMod 8) ∉ T := by
    intro h
    have hs := (Finset.mem_filter.mp h).2.1
    exact hneg _ (by simpa using hflip 0) hs
  have hpq : (-1 : ZMod 8) ≠ 1 := by decide
  have hins : insert (-1) (insert 1 T) ⊆ R := by
    intro j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hminus⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hplus⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.2⟩
  have hcard : (insert (-1) (insert 1 T)).card = T.card + 2 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem hqT]
    · simp [hpT, hpq]
  have hle := Finset.card_le_card hins
  simpa [T, R, hcard] using hle

/-- An internal row of size `7-r` whose two cycle entries are present forces
the signed capacity upper bound `r+k≤5`. -/
theorem alternating_C8_allTriangleFree_internal_parameter_upper
    (N : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ) (k r : ℕ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r)
    (hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f 0 ∧ N 0 j = 1).card = k)
    (hminus : N 0 (-1) = 1) (hplus : N 0 1 = 1) :
    r + k ≤ 5 := by
  have hle := alternating_C8_row_same_add_two_le_of_cycleOnes
    N f hsign hflip hminus hplus
  rw [hNrow, hNsame] at hle
  omega

end


end Erdos85

#print axioms Erdos85.alternating_C8_row_same_add_two_le_of_cycleOnes
#print axioms Erdos85.alternating_C8_allTriangleFree_internal_parameter_upper
