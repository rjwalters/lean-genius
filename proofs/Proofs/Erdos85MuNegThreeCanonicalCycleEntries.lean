import Proofs.Erdos85SizeTwoMuNegThreeRefinedSectorRouting

/-!
# Cycle-entry reduction for canonical `mu = -3` endpoints

The refined sector predicate records the shore geometry and the same `(k,r)`
used by the switch orbit.  A cell outside the both-triangle and mixed
parameter tables must therefore lie in the both-triangle-free branch.
-/

namespace Erdos85

noncomputable section

/-- Eliminate the two non-TF branches of the refined μ=-3 sector table using
only parameter nonmembership. -/
theorem muNegThree_refined_bothCycleEntriesOne_of_not_triangle_or_mixed
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hcell : MuNegThreeRefinedSectorCells N₁ N₂ k r)
    (htri : ¬ MuNegThreeBothTriangleCell k r)
    (hmixed : ¬ MuNegThreeMixedCell k r) :
    C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ := by
  rcases hcell with hzero | hmix | hone
  · exact False.elim (htri hzero.2.2)
  · exact False.elim (hmixed hmix.2)
  · exact ⟨hone.1, hone.2.1⟩

/-- The canonical cross-orbit endpoint `h313 = (-3,1,3)` has two
all-cycle-entries-one shores. -/
theorem muNegThree_oneThree_bothCycleEntriesOne
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hcell : MuNegThreeRefinedSectorCells N₁ N₂ 1 3) :
    C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ := by
  apply muNegThree_refined_bothCycleEntriesOne_of_not_triangle_or_mixed
    N₁ N₂ 1 3 hcell
  · simp [MuNegThreeBothTriangleCell]
  · simp [MuNegThreeMixedCell]

end

end Erdos85

#print axioms Erdos85.muNegThree_refined_bothCycleEntriesOne_of_not_triangle_or_mixed
#print axioms Erdos85.muNegThree_oneThree_bothCycleEntriesOne
