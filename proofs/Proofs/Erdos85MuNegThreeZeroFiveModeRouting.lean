import Proofs.Erdos85SizeTwoMuNegThreeRefinedSectorRouting

/-!
# Exact shore-mode routing for the canonical `h305` endpoint

Unlike `h313`, the `(mu,k,r)=(-3,0,5)` cell genuinely occurs in every shore
mode of the refined sector grid.  This file removes the now-fixed arithmetic
payload and exposes the exact three geometry callbacks a terminal must close.
-/

namespace Erdos85

noncomputable section

/-- At `h305`, the refined sector predicate is exactly: both shores have
zero cycle entries, exactly one does, or both have cycle entries one. -/
theorem muNegThree_zeroFive_refinedSectorCells_iff_modes
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) :
    MuNegThreeRefinedSectorCells N₁ N₂ 0 5 ↔
      (C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂) ∨
      ((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
        (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∨
      (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂) := by
  constructor
  · intro hcell
    rcases hcell with hzero | hmixed | hone
    · exact Or.inl ⟨hzero.1, hzero.2.1⟩
    · exact Or.inr (Or.inl hmixed.1)
    · exact Or.inr (Or.inr ⟨hone.1, hone.2.1⟩)
  · intro hmodes
    rcases hmodes with hzero | hmixed | hone
    · left
      exact ⟨hzero.1, hzero.2, by simp [MuNegThreeBothTriangleCell]⟩
    · right; left
      exact ⟨hmixed, by simp [MuNegThreeMixedCell]⟩
    · right; right
      exact ⟨hone.1, hone.2, by simp⟩

/-- Callback form used by a three-certificate terminal assembly. -/
theorem muNegThree_zeroFive_false_of_three_mode_terminals
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hcell : MuNegThreeRefinedSectorCells N₁ N₂ 0 5)
    (hzero : C8CycleEntriesZero N₁ → C8CycleEntriesZero N₂ → False)
    (hmixed :
      ((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
        (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) → False)
    (hone : C8CycleEntriesOne N₁ → C8CycleEntriesOne N₂ → False) : False := by
  rcases (muNegThree_zeroFive_refinedSectorCells_iff_modes N₁ N₂).mp hcell with
      hz | hm | ho
  · exact hzero hz.1 hz.2
  · exact hmixed hm
  · exact hone ho.1 ho.2

end

end Erdos85

#print axioms Erdos85.muNegThree_zeroFive_refinedSectorCells_iff_modes
#print axioms Erdos85.muNegThree_zeroFive_false_of_three_mode_terminals
