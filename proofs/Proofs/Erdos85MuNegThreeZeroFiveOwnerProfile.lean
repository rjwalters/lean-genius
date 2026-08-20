import Proofs.Erdos85MuNegThreeOneThreeOwnerProfile
import Proofs.Erdos85MuNegThreeZeroFiveModeRouting

/-!
# The common cross-owner profile of the h305 shore modes

The canonical `(-3,0,5)` endpoint has three possible within-shore mode
families.  Their cross block is nevertheless uniform: every row and column
has three exterior pairs, two same-sign and one opposite-sign.  This separates
the common cross-owner semantics from the three mode-specific same-shore
owner universes.
-/

open Finset Matrix

namespace Erdos85

noncomputable section

theorem muNegThree_zeroFive_crossExteriorProfile
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L₁ : MuNegThreeExplicitParameterLedger N₁ M₁ f g 0 5)
    (L₂ : MuNegThreeExplicitParameterLedger N₂ M₂ g f 0 5)
    (htranspose : ∀ i j, M₂ j i = M₁ i j) :
    MuNegFiveCrossExteriorProfile M₁ f g 3 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa using L₁.crossExterior_total_card i
  · intro i
    exact (L₁.zeroFive_crossExterior_split i).1
  · intro j
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ M₁ i j ≠ 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ M₂ j i ≠ 1) by
      ext i
      simp [htranspose i j]]
    simpa using L₂.crossExterior_total_card j
  · intro j
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        f i = g j ∧ M₁ i j ≠ 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
          f i = g j ∧ M₂ j i ≠ 1) by
      ext i
      simp [htranspose i j]]
    exact (L₂.zeroFive_crossExterior_split j).1

/-- Complete h305 parameter socket: one of the three exact shore-mode
families, together with the mode-independent `(total,same) = (3,2)` cross
profile. -/
theorem muNegThree_zeroFive_ownerProfile
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (hcell : MuNegThreeRefinedSectorCells N₁ N₂ 0 5)
    (L₁ : MuNegThreeExplicitParameterLedger N₁ M₁ f g 0 5)
    (L₂ : MuNegThreeExplicitParameterLedger N₂ M₂ g f 0 5)
    (htranspose : ∀ i j, M₂ j i = M₁ i j) :
    ((C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂) ∨
      ((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
        (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∨
      (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂)) ∧
      MuNegFiveCrossExteriorProfile M₁ f g 3 2 := by
  exact ⟨(muNegThree_zeroFive_refinedSectorCells_iff_modes N₁ N₂).mp hcell,
    muNegThree_zeroFive_crossExteriorProfile L₁ L₂ htranspose⟩

end

end Erdos85

#print axioms Erdos85.muNegThree_zeroFive_crossExteriorProfile
#print axioms Erdos85.muNegThree_zeroFive_ownerProfile
