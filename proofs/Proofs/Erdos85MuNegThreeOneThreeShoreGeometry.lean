import Proofs.Erdos85MuNegFiveZeroFourShoreGeometry
import Proofs.Erdos85MuNegThreeOneThreeOwnerProfile

/-! # Shore-degree audit for the `mu=-3`, `(k,r)=(1,3)` endpoint -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- Every h313 diagonal defect lies at an odd offset or at the antipode. -/
theorem MuNegThreeExplicitParameterLedger.oneThree_internal_imp_oddOrFour
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegThreeExplicitParameterLedger N M f g 1 3)
    (hshape : ZModEightSameSignShape N f 1) :
    ∀ i j : ZMod 8, N i j = 1 →
      j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
        j - i = 5 ∨ j - i = 7 := by
  rcases hshape with hzero | hone | htwo
  · omega
  · obtain ⟨_, hone⟩ := hone
    intro i j hij
    by_cases hodd : j - i = 1 ∨ j - i = 3 ∨
        j - i = 5 ∨ j - i = 7
    · rcases hodd with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · have heven := zmodEight_not_oddOffset_imp_evenOffset (j - i) hodd
      have hsame := (zmodEight_alternating_sign_eq_iff_evenOffset
        f L.f_sign L.f_flip i j).mpr heven
      exact Or.inr (Or.inr (Or.inl ((hone i j hsame).mp hij)))
  · omega

/-- The normalized h313 row has exactly one nondefect among offsets `3,5`.
Thus its within-shore exterior degree is one, not two. -/
theorem MuNegThreeExplicitParameterLedger.oneThree_anchor_middleOdd_nondefect_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegThreeExplicitParameterLedger N M f g 1 3)
    (hshape : ZModEightSameSignShape N f 1)
    (hcycle : C8CycleEntriesOne N) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (j - 0 = 3 ∨ j - 0 = 5) ∧ N 0 j ≠ 1).card = 1 := by
  classical
  let A := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1
  let O := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    j - 0 = 1 ∨ j - 0 = 3 ∨ j - 0 = 4 ∨
      j - 0 = 5 ∨ j - 0 = 7
  have hAcard : A.card = 4 := by simpa [A] using L.internal_row 0
  have hOcard : O.card = 5 := by
    simpa [O] using zmodEight_oddOrFour_card_five 0
  have hAO : A ⊆ O := by
    intro j hj
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      L.oneThree_internal_imp_oddOrFour hshape 0 j hj⟩
  have hdiff : (O \ A).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAO, hOcard, hAcard]
  have heq : O \ A =
      (Finset.univ : Finset (ZMod 8)).filter (fun j ↦
        (j - 0 = 3 ∨ j - 0 = 5) ∧ N 0 j ≠ 1) := by
    ext j
    simp only [O, A, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hoff, hnot⟩
      rcases hoff with h1 | h3 | h4 | h5 | h7
      · exfalso; apply hnot
        have hj : j = 1 := by simpa using h1
        simpa [hj] using hcycle.2
      · exact ⟨Or.inl h3, hnot⟩
      · exfalso; apply hnot
        rcases hshape with hzero | hone | htwo
        · omega
        · have hsame : f j = f 0 :=
            (zmodEight_alternating_sign_eq_iff_evenOffset
              f L.f_sign L.f_flip 0 j).mpr (by
                rw [h4]
                decide)
          exact (hone.2 0 j hsame).mpr h4
        · omega
      · exact ⟨Or.inr h5, hnot⟩
      · exfalso; apply hnot
        have hj : j = -1 := by
          calc j = 7 := by simpa using h7
               _ = -1 := by decide
        simpa [hj] using hcycle.1
    · rintro ⟨hmid, hnot⟩
      exact ⟨hmid.elim (fun h ↦ Or.inr (Or.inl h))
        (fun h ↦ Or.inr (Or.inr (Or.inr (Or.inl h)))), hnot⟩
  rw [← heq]
  exact hdiff

end

end Erdos85

#print axioms Erdos85.MuNegThreeExplicitParameterLedger.oneThree_internal_imp_oddOrFour
#print axioms Erdos85.MuNegThreeExplicitParameterLedger.oneThree_anchor_middleOdd_nondefect_card
