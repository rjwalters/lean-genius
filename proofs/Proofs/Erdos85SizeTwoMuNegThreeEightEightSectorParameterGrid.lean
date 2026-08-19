import Proofs.Erdos85SizeTwoMuNegThreeEightEightAllTriangleFreeParameterBounds
import Proofs.Erdos85SizeTwoMuNegThreeEightEightNormalForm
import Proofs.Erdos85SizeTwoEigenlineInternalCycleSectorDichotomy

/-! # The shared signed-parameter grid for two C8 sectors -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- The two distinguished cycle entries of a normalized C8 row vanish. -/
def C8CycleEntriesZero (N : Matrix (ZMod 8) (ZMod 8) ℤ) : Prop :=
  N 0 (-1) ≠ 1 ∧ N 0 1 ≠ 1

/-- The two distinguished cycle entries of a normalized C8 row occur. -/
def C8CycleEntriesOne (N : Matrix (ZMod 8) (ZMod 8) ℤ) : Prop :=
  N 0 (-1) = 1 ∧ N 0 1 = 1

/-- With one common `(k,r)` ledger, the two shore colors give a three-cell
parameter grid: both all-triangle, mixed (forcing capacity five), or both
all-triangle-free. -/
theorem alternating_C8_twoShore_sector_parameter_grid
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f₁ f₂ : ZMod 8 → ℤ) (k r : ℕ)
    (hsign₁ : ∀ i, f₁ i = -1 ∨ f₁ i = 1)
    (hsign₂ : ∀ i, f₂ i = -1 ∨ f₂ i = 1)
    (hflip₁ : ∀ i, f₁ (i + 1) = -f₁ i)
    (hflip₂ : ∀ i, f₂ (i + 1) = -f₂ i)
    (hrow₁ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N₁ 0 j = 1).card = 7 - r)
    (hrow₂ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N₂ 0 j = 1).card = 7 - r)
    (hsame₁ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f₁ j = f₁ 0 ∧ N₁ 0 j = 1).card = k)
    (hsame₂ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f₂ j = f₂ 0 ∧ N₂ 0 j = 1).card = k)
    (hsector₁ : C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁)
    (hsector₂ : C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂) :
    (C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂ ∧ 5 ≤ r + k) ∨
      (((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
          (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∧ r + k = 5) ∨
      (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ ∧ r + k ≤ 5) := by
  rcases hsector₁ with hz₁ | ho₁ <;> rcases hsector₂ with hz₂ | ho₂
  · left
    exact ⟨hz₁, hz₂,
      alternating_C8_allTriangle_internal_parameter_lower
        N₁ f₁ k r hsign₁ hflip₁ hrow₁ hsame₁ hz₁.1 hz₁.2⟩
  · right; left
    refine ⟨Or.inl ⟨hz₁, ho₂⟩, ?_⟩
    have hlo := alternating_C8_allTriangle_internal_parameter_lower
      N₁ f₁ k r hsign₁ hflip₁ hrow₁ hsame₁ hz₁.1 hz₁.2
    have hhi := alternating_C8_allTriangleFree_internal_parameter_upper
      N₂ f₂ k r hsign₂ hflip₂ hrow₂ hsame₂ ho₂.1 ho₂.2
    omega
  · right; left
    refine ⟨Or.inr ⟨ho₁, hz₂⟩, ?_⟩
    have hlo := alternating_C8_allTriangle_internal_parameter_lower
      N₂ f₂ k r hsign₂ hflip₂ hrow₂ hsame₂ hz₂.1 hz₂.2
    have hhi := alternating_C8_allTriangleFree_internal_parameter_upper
      N₁ f₁ k r hsign₁ hflip₁ hrow₁ hsame₁ ho₁.1 ho₁.2
    omega
  · right; right
    exact ⟨ho₁, ho₂,
      alternating_C8_allTriangleFree_internal_parameter_upper
        N₁ f₁ k r hsign₁ hflip₁ hrow₁ hsame₁ ho₁.1 ho₁.2⟩

end


end Erdos85

#print axioms Erdos85.alternating_C8_twoShore_sector_parameter_grid
