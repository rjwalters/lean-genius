import Proofs.Erdos85MuNegThreeExplicitParameters
import Proofs.Erdos85MuNegThreeCanonicalCycleEntries
import Proofs.Erdos85MuNegFiveCanonicalCrossProfiles

/-!
# h313 has the h503 owner profile

At the canonical `(-3,1,3)` endpoint both shores are all-cycle-entries-one.
Its exterior cross block has degree five with signed split `3+2`, in every row
and column.  Thus its finite owner model is exactly the already-certified h503
model; this file records the parameter-level identification.
-/

open Finset Matrix

namespace Erdos85

noncomputable section

theorem MuNegThreeExplicitParameterLedger.crossExterior_total_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegThreeExplicitParameterLedger N M f g k r) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M i j ≠ 1).card = 8 - r := by
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ M i j = 1) (s := (Finset.univ : Finset (ZMod 8)))
  rw [L.cross_row i] at hpart
  norm_num at hpart ⊢
  omega

theorem muNegThree_oneThree_crossExteriorProfile
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L₁ : MuNegThreeExplicitParameterLedger N₁ M₁ f g 1 3)
    (L₂ : MuNegThreeExplicitParameterLedger N₂ M₂ g f 1 3)
    (htranspose : ∀ i j, M₂ j i = M₁ i j) :
    MuNegFiveCrossExteriorProfile M₁ f g 5 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa using L₁.crossExterior_total_card i
  · intro i
    exact (L₁.oneThree_crossExterior_split i).1
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
    exact (L₂.oneThree_crossExterior_split j).1

/-- The complete h313 parameter socket: both fixed shores are in the same
all-cycle-entries-one mode used by h503, and the cross exterior relation has
the identical `(5,3)` row-and-column profile. -/
theorem muNegThree_oneThree_h503OwnerProfile
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (hcell : MuNegThreeRefinedSectorCells N₁ N₂ 1 3)
    (L₁ : MuNegThreeExplicitParameterLedger N₁ M₁ f g 1 3)
    (L₂ : MuNegThreeExplicitParameterLedger N₂ M₂ g f 1 3)
    (htranspose : ∀ i j, M₂ j i = M₁ i j) :
    (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂) ∧
      MuNegFiveCrossExteriorProfile M₁ f g 5 3 := by
  exact ⟨muNegThree_oneThree_bothCycleEntriesOne N₁ N₂ hcell,
    muNegThree_oneThree_crossExteriorProfile L₁ L₂ htranspose⟩

end

end Erdos85

#print axioms Erdos85.muNegThree_oneThree_h503OwnerProfile
