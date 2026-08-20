import Proofs.Erdos85MuNegFiveZeroFourShoreGeometry

/-! # Intertwiner obstruction at the `mu=-5`, `(k,r)=(0,4)` endpoint -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- With the cycle entries present in every row, every row has exactly one
nondefect among its two middle-odd offsets. -/
theorem MuNegFiveExplicitRowParameterLedger.zeroFour_middleOdd_nondefect_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 4)
    (hshape : ZModEightSameSignShape N f 0)
    (hcycle : ∀ i, N i (i - 1) = 1 ∧ N i (i + 1) = 1)
    (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (j - i = 3 ∨ j - i = 5) ∧ N i j ≠ 1).card = 1 := by
  classical
  let A := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N i j = 1
  let O := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7
  have hAcard : A.card = 3 := by simpa [A] using L.internal_row i
  have hOcard : O.card = 4 := by
    simpa [O] using zmodEight_oddOffset_card_four i
  have hAO : A ⊆ O := by
    intro j hj
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      L.zeroFour_internal_imp_odd hshape i j hj⟩
  have hdiff : (O \ A).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAO, hOcard, hAcard]
  have heq : O \ A =
      (Finset.univ : Finset (ZMod 8)).filter (fun j ↦
        (j - i = 3 ∨ j - i = 5) ∧ N i j ≠ 1) := by
    ext j
    simp only [O, A, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hoff, hnot⟩
      rcases hoff with h1 | h3 | h5 | h7
      · exfalso; apply hnot
        have hj : j = i + 1 := by linear_combination h1
        simpa [hj] using (hcycle i).2
      · exact ⟨Or.inl h3, hnot⟩
      · exact ⟨Or.inr h5, hnot⟩
      · exfalso; apply hnot
        have hj : j = i - 1 := by
          have hseven : (7 : ZMod 8) = -1 := by decide
          rw [hseven] at h7
          linear_combination h7
        simpa [hj] using (hcycle i).1
    · rintro ⟨hmid, hnot⟩
      exact ⟨hmid.elim (fun h ↦ Or.inr (Or.inl h))
        (fun h ↦ Or.inr (Or.inr (Or.inl h))), hnot⟩
  rw [← heq]
  exact hdiff

/-- Consequently exactly one middle-odd entry is a defect. -/
theorem MuNegFiveExplicitRowParameterLedger.zeroFour_middleOdd_choice
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 4)
    (hshape : ZModEightSameSignShape N f 0)
    (hcycle : ∀ i, N i (i - 1) = 1 ∧ N i (i + 1) = 1)
    (i : ZMod 8) :
    (N i (i + 3) ≠ 1 ∧ N i (i + 5) = 1) ∨
      (N i (i + 3) = 1 ∧ N i (i + 5) ≠ 1) := by
  classical
  let S := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    (j - i = 3 ∨ j - i = 5) ∧ N i j ≠ 1
  have hcard : S.card = 1 := by
    simpa [S] using L.zeroFour_middleOdd_nondefect_card hshape hcycle i
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hxmem : x ∈ S := by simp [hx]
  have hxoff : x = i + 3 ∨ x = i + 5 := by
    have := (Finset.mem_filter.mp hxmem).2.1
    rcases this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hxoff with rfl | rfl
  · left
    have hne3 : N i (i + 3) ≠ 1 := (Finset.mem_filter.mp hxmem).2.2
    refine ⟨hne3, by_contra fun hne5 ↦ ?_⟩
    have hm : i + 5 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      refine ⟨Or.inr ?_, hne5⟩
      ring⟩
    rw [hx] at hm
    have heq : i + 5 = i + 3 := by simpa using hm
    have : ¬ ((5 : ZMod 8) = 3) := by decide
    apply this
    linear_combination heq
  · right
    have hne5 : N i (i + 5) ≠ 1 := (Finset.mem_filter.mp hxmem).2.2
    refine ⟨by_contra fun hne3 ↦ ?_, hne5⟩
    have hm : i + 3 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      refine ⟨Or.inl ?_, hne3⟩
      ring⟩
    rw [hx] at hm
    have heq : i + 3 = i + 5 := by simpa using hm
    have : ¬ ((3 : ZMod 8) = 5) := by decide
    apply this
    linear_combination heq

/-- A symmetric h504 diagonal block with all cycle entries cannot satisfy
the cycle-intertwining equation.  Intertwining makes the offset-three choice
constant from row to row, whereas symmetry exchanges offsets three and five. -/
theorem MuNegFiveExplicitRowParameterLedger.zeroFour_false_of_intertwine
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 4)
    (hshape : ZModEightSameSignShape N f 0)
    (hcycle : ∀ i, N i (i - 1) = 1 ∧ N i (i + 1) = 1)
    (hsymm : ∀ i j, N i j = N j i)
    (hinter : ∀ i j,
      N (i - 1) j + N (i + 1) j = N i (j + 1) + N i (j - 1)) :
    False := by
  let x : ZMod 8 → ℤ := fun i ↦ N i (i + 3)
  have hstep (i : ZMod 8) : x (i - 1) = x i := by
    have h := hinter i (i + 2)
    have hc₁ : N (i + 1) (i + 2) = 1 := by
      convert (hcycle (i + 1)).2 using 1 <;> ring
    have hc₀ : N i (i + 1) = 1 := (hcycle i).2
    have hm₁ : N (i - 1) (i + 2) = x (i - 1) := by
      dsimp only [x]
      congr 1
      ring
    have hm₀ : N i (i + 3) = x i := rfl
    have hp : i + 2 + 1 = i + 3 := by ring
    have hm : i + 2 - 1 = i + 1 := by ring
    rw [hp, hm] at h
    rw [hc₁, hc₀, hm₁, hm₀] at h
    omega
  have hs01 : x 0 = x 1 := by
    have h := hstep 1
    have hz : (1 - 1 : ZMod 8) = 0 := by decide
    rwa [hz] at h
  have hs12 : x 1 = x 2 := by
    have h := hstep 2
    have hz : (2 - 1 : ZMod 8) = 1 := by decide
    rwa [hz] at h
  have hs23 : x 2 = x 3 := by
    have h := hstep 3
    have hz : (3 - 1 : ZMod 8) = 2 := by decide
    rwa [hz] at h
  have hs34 : x 3 = x 4 := by
    have h := hstep 4
    have hz : (4 - 1 : ZMod 8) = 3 := by decide
    rwa [hz] at h
  have hs45 : x 4 = x 5 := by
    have h := hstep 5
    have hz : (5 - 1 : ZMod 8) = 4 := by decide
    rwa [hz] at h
  have hx03 : x 0 = x 3 := by
    exact hs01.trans (hs12.trans hs23)
  have hx05 : x 0 = x 5 := by
    exact hx03.trans (hs34.trans hs45)
  rcases L.zeroFour_middleOdd_choice hshape hcycle 0 with h05 | h03
  · have hx5 : x 5 = 1 := by
      dsimp only [x]
      have h50 : (5 + 3 : ZMod 8) = 0 := by decide
      rw [h50, hsymm]
      simpa using h05.2
    exact h05.1 (by simpa [x] using hx05.trans hx5)
  · have hx3 : x 3 = 1 := hx03.symm.trans (by simpa [x] using h03.1)
    rcases L.zeroFour_middleOdd_choice hshape hcycle 3 with h30 | h36
    · exact h30.1 hx3
    · apply h36.2
      have h30eq : (3 + 5 : ZMod 8) = 0 := by decide
      rw [h30eq, hsymm]
      simpa using h03.1

end

end Erdos85

#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroFour_middleOdd_nondefect_card
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroFour_middleOdd_choice
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroFour_false_of_intertwine
