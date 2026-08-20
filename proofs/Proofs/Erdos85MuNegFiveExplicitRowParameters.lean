import Proofs.Erdos85MuNegFiveExplicitParameters

/-!
# Every-row parameter ledger for the canonical `mu = -5` endpoints

The original explicit ledger records coordinate zero, which is sufficient for
the capacity argument.  Finite owner semantics need the same defect and sign
counts in every row (and, after swapping shores, in every column).  This file
packages that stronger interface and derives the exact exterior splits used by
the three canonical endpoints.
-/

open Finset Matrix

namespace Erdos85

noncomputable section

structure MuNegFiveExplicitRowParameterLedger
    (N M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ) (k r : ℕ) : Prop where
  k_le_one : k ≤ 1
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
      g j = f i ∧ M i j = 1).card = 1 - k

theorem MuNegFiveExplicitRowParameterLedger.toExplicitParameterLedger
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g k r) :
    MuNegFiveExplicitParameterLedger N M f g k r :=
  ⟨L.k_le_one, L.f_sign, L.g_sign, L.f_flip, L.g_flip,
    L.internal_row 0, L.internal_same 0, L.cross_row 0, L.cross_same 0⟩

theorem MuNegFiveExplicitRowParameterLedger.crossExterior_same_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g k r) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j ≠ 1).card = 3 + k := by
  classical
  let S := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ g j = f i
  have hScard : S.card = 4 :=
    (zmodEight_alternating_sign_class_cards_four
      g L.g_sign L.g_flip (f i) (L.f_sign i)).1
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ M i j = 1) (s := S)
  have hyes : (S.filter fun j ↦ M i j = 1).card = 1 - k := by
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

theorem MuNegFiveExplicitRowParameterLedger.crossExterior_opp_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g k r) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j ≠ f i ∧ M i j ≠ 1).card = 5 - (r + k) := by
  classical
  let D := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ M i j = 1
  have hDpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ g j = f i) (s := D)
  have hDsame : (D.filter fun j ↦ g j = f i).card = 1 - k := by
    rw [show (D.filter fun j ↦ g j = f i) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          g j = f i ∧ M i j = 1) by
      ext j
      simp [D, and_comm]]
    exact L.cross_same i
  have hDopp : (D.filter fun j ↦ ¬ g j = f i).card = r - (1 - k) := by
    have hDcard : D.card = r := by simpa [D] using L.cross_row i
    rw [hDcard, hDsame] at hDpart
    omega
  have hr_lower : 1 - k ≤ r := by
    have hDcard : D.card = r := by simpa [D] using L.cross_row i
    rw [hDcard, hDsame] at hDpart
    omega
  let O := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ g j ≠ f i
  have hOcard : O.card = 4 :=
    (zmodEight_alternating_sign_class_cards_four
      g L.g_sign L.g_flip (f i) (L.f_sign i)).2
  have hOpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ M i j = 1) (s := O)
  have hOyes : (O.filter fun j ↦ M i j = 1).card = r - (1 - k) := by
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
  have hcross := L.cross_row i
  have hsame := L.cross_same i
  omega

theorem MuNegFiveExplicitRowParameterLedger.zeroThree_crossExterior_split
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 3) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j ≠ 1).card = 3 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j ≠ f i ∧ M i j ≠ 1).card = 2 := by
  simpa using ⟨L.crossExterior_same_card i, L.crossExterior_opp_card i⟩

theorem MuNegFiveExplicitRowParameterLedger.zeroFour_crossExterior_split
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 4) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j ≠ 1).card = 3 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j ≠ f i ∧ M i j ≠ 1).card = 1 := by
  simpa using ⟨L.crossExterior_same_card i, L.crossExterior_opp_card i⟩

theorem MuNegFiveExplicitRowParameterLedger.oneTwo_crossExterior_split
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 1 2) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f i ∧ M i j ≠ 1).card = 4 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j ≠ f i ∧ M i j ≠ 1).card = 2 := by
  simpa using ⟨L.crossExterior_same_card i, L.crossExterior_opp_card i⟩

end

end Erdos85

#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.crossExterior_same_card
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.crossExterior_opp_card
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroThree_crossExterior_split
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroFour_crossExterior_split
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.oneTwo_crossExterior_split
