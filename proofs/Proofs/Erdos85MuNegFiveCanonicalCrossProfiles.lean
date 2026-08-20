import Proofs.Erdos85MuNegFiveExplicitRowParameters

/-!
# Row-and-column cross profiles for the canonical `mu = -5` endpoints

Owner CNFs view the exterior cross relation as an `8 × 8` Boolean block.
The two oriented every-row ledgers supply its rows and columns.  This file
turns them into the compact profile consumed by finite semantics.
-/

open Finset Matrix

namespace Erdos85

noncomputable section

structure MuNegFiveCrossExteriorProfile
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ) (total same : ℕ) : Prop where
  row_total : ∀ i,
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M i j ≠ 1).card = total
  row_same : ∀ i,
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j ≠ 1).card = same
  col_total : ∀ j,
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ M i j ≠ 1).card = total
  col_same : ∀ j,
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      f i = g j ∧ M i j ≠ 1).card = same

theorem MuNegFiveExplicitRowParameterLedger.crossExterior_total_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g k r) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M i j ≠ 1).card = 8 - r := by
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ M i j = 1) (s := (Finset.univ : Finset (ZMod 8)))
  rw [L.cross_row i] at hpart
  norm_num at hpart ⊢
  omega

theorem muNegFive_crossExteriorProfile_of_orientedLedgers
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L₁ : MuNegFiveExplicitRowParameterLedger N₁ M₁ f g k r)
    (L₂ : MuNegFiveExplicitRowParameterLedger N₂ M₂ g f k r)
    (htranspose : ∀ i j, M₂ j i = M₁ i j) :
    MuNegFiveCrossExteriorProfile M₁ f g (8 - r) (3 + k) := by
  refine ⟨L₁.crossExterior_total_card, L₁.crossExterior_same_card, ?_, ?_⟩
  · intro j
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ M₁ i j ≠ 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ M₂ j i ≠ 1) by
      ext i
      simp [htranspose i j]]
    exact L₂.crossExterior_total_card j
  · intro j
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        f i = g j ∧ M₁ i j ≠ 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
          f i = g j ∧ M₂ j i ≠ 1) by
      ext i
      simp [htranspose i j]]
    exact L₂.crossExterior_same_card j

theorem muNegFive_zeroThree_crossExteriorProfile
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L₁ : MuNegFiveExplicitRowParameterLedger N₁ M₁ f g 0 3)
    (L₂ : MuNegFiveExplicitRowParameterLedger N₂ M₂ g f 0 3)
    (htranspose : ∀ i j, M₂ j i = M₁ i j) :
    MuNegFiveCrossExteriorProfile M₁ f g 5 3 := by
  simpa using muNegFive_crossExteriorProfile_of_orientedLedgers
    L₁ L₂ htranspose

theorem muNegFive_zeroFour_crossExteriorProfile
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L₁ : MuNegFiveExplicitRowParameterLedger N₁ M₁ f g 0 4)
    (L₂ : MuNegFiveExplicitRowParameterLedger N₂ M₂ g f 0 4)
    (htranspose : ∀ i j, M₂ j i = M₁ i j) :
    MuNegFiveCrossExteriorProfile M₁ f g 4 3 := by
  simpa using muNegFive_crossExteriorProfile_of_orientedLedgers
    L₁ L₂ htranspose

theorem muNegFive_oneTwo_crossExteriorProfile
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L₁ : MuNegFiveExplicitRowParameterLedger N₁ M₁ f g 1 2)
    (L₂ : MuNegFiveExplicitRowParameterLedger N₂ M₂ g f 1 2)
    (htranspose : ∀ i j, M₂ j i = M₁ i j) :
    MuNegFiveCrossExteriorProfile M₁ f g 6 4 := by
  simpa using muNegFive_crossExteriorProfile_of_orientedLedgers
    L₁ L₂ htranspose

end


end Erdos85

#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.crossExterior_total_card
#print axioms Erdos85.muNegFive_crossExteriorProfile_of_orientedLedgers
#print axioms Erdos85.muNegFive_zeroThree_crossExteriorProfile
#print axioms Erdos85.muNegFive_zeroFour_crossExteriorProfile
#print axioms Erdos85.muNegFive_oneTwo_crossExteriorProfile
