import Proofs.Erdos85SizeTwoMuNegThreeEightEightParameterBounds

/-!
# Explicit parameter ledger for canonical `mu = -3` endpoints

Certificate adapters need row facts for the same `(k,r)` retained by the
switch orbit.  This structure is the coordinate-level handshake: defect
degree `r` across the two shores, same-sign defect degree `2-k`, alternating
signs, and the sharp global parameter window.  The derived lemmas give the
corresponding exterior (defect-complement) sign counts in every row.
-/

open Finset Matrix

namespace Erdos85

noncomputable section

structure MuNegThreeExplicitParameterLedger
    (N M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ) (k r : ℕ) : Prop where
  k_le_one : k ≤ 1
  sum_le_six : r + k ≤ 6
  f_sign : ∀ i, f i = -1 ∨ f i = 1
  g_sign : ∀ j, g j = -1 ∨ g j = 1
  f_flip : ∀ i, f (i + 1) = -f i
  g_flip : ∀ j, g (j + 1) = -g j
  internal_row : ∀ i,
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N i j = 1).card = 7 - r
  internal_same : ∀ i,
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f i ∧ N i j = 1).card = k
  cross_row : ∀ i,
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M i j = 1).card = r
  cross_same : ∀ i,
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j = 1).card = 2 - k

/-- In each cross row, exterior (nondefect) pairs of the same sign number
`2+k`. -/
theorem MuNegThreeExplicitParameterLedger.crossExterior_same_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegThreeExplicitParameterLedger N M f g k r) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j ≠ 1).card = 2 + k := by
  classical
  let S := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ g j = f i
  have hScard : S.card = 4 := by
    exact (zmodEight_alternating_sign_class_cards_four
      g L.g_sign L.g_flip (f i) (L.f_sign i)).1
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ M i j = 1) (s := S)
  have hyes : (S.filter fun j ↦ M i j = 1).card = 2 - k := by
    rw [show (S.filter fun j ↦ M i j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          g j = f i ∧ M i j = 1) by
      ext j
      simp [S]]
    exact L.cross_same i
  have hno : (S.filter fun j ↦ ¬ M i j = 1) =
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        g j = f i ∧ M i j ≠ 1) := by
    ext j
    simp [S]
  rw [hScard, hyes, hno] at hpart
  have hk := L.k_le_one
  omega

/-- In each cross row, exterior (nondefect) pairs of the opposite sign number
`6-(r+k)`. -/
theorem MuNegThreeExplicitParameterLedger.crossExterior_opp_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegThreeExplicitParameterLedger N M f g k r) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j ≠ f i ∧ M i j ≠ 1).card = 6 - (r + k) := by
  classical
  let D := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ M i j = 1
  have hDpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ g j = f i) (s := D)
  have hDsame : (D.filter fun j ↦ g j = f i).card = 2 - k := by
    rw [show (D.filter fun j ↦ g j = f i) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          g j = f i ∧ M i j = 1) by
      ext j
      simp [D, and_comm]]
    exact L.cross_same i
  have hDopp : (D.filter fun j ↦ ¬ g j = f i).card = r - (2 - k) := by
    have hDcard : D.card = r := by simpa [D] using L.cross_row i
    rw [hDcard, hDsame] at hDpart
    omega
  have hr : 2 - k ≤ r := by
    have hDcard : D.card = r := by simpa [D] using L.cross_row i
    rw [hDcard, hDsame] at hDpart
    omega
  let O := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ g j ≠ f i
  have hOcard : O.card = 4 := by
    exact (zmodEight_alternating_sign_class_cards_four
      g L.g_sign L.g_flip (f i) (L.f_sign i)).2
  have hOpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ M i j = 1) (s := O)
  have hOyes : (O.filter fun j ↦ M i j = 1).card = r - (2 - k) := by
    rw [show (O.filter fun j ↦ M i j = 1) =
        (D.filter fun j ↦ ¬ g j = f i) by
      ext j
      simp [O, D, and_comm]]
    exact hDopp
  have hOno : (O.filter fun j ↦ ¬ M i j = 1) =
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        g j ≠ f i ∧ M i j ≠ 1) := by
    ext j
    simp [O]
  rw [hOcard, hOyes, hOno] at hOpart
  have hk := L.k_le_one
  have hsum := L.sum_le_six
  omega

/-- Cross exterior sign split at `h313=(-3,1,3)`: three same-sign and two
opposite-sign owners in every row. -/
theorem MuNegThreeExplicitParameterLedger.oneThree_crossExterior_split
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegThreeExplicitParameterLedger N M f g 1 3) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j ≠ 1).card = 3 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j ≠ f i ∧ M i j ≠ 1).card = 2 := by
  simpa using ⟨L.crossExterior_same_card i, L.crossExterior_opp_card i⟩

/-- Cross exterior sign split at `h305=(-3,0,5)`: two same-sign and one
opposite-sign owner in every row, independently of its shore mode. -/
theorem MuNegThreeExplicitParameterLedger.zeroFive_crossExterior_split
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegThreeExplicitParameterLedger N M f g 0 5) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j ≠ 1).card = 2 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j ≠ f i ∧ M i j ≠ 1).card = 1 := by
  simpa using ⟨L.crossExterior_same_card i, L.crossExterior_opp_card i⟩

end

end Erdos85

#print axioms Erdos85.MuNegThreeExplicitParameterLedger.crossExterior_same_card
#print axioms Erdos85.MuNegThreeExplicitParameterLedger.crossExterior_opp_card
#print axioms Erdos85.MuNegThreeExplicitParameterLedger.oneThree_crossExterior_split
#print axioms Erdos85.MuNegThreeExplicitParameterLedger.zeroFive_crossExterior_split
