import Proofs.Erdos85CrossNeighborhoodFlipDefectExpansion

/-!
# Localization of exported overlap in the active wedge ledger

This file formalizes the finite support statements in
`(73rnz_cjibkzzzf)--(73rnz_cjibkzzzha)`.  A size-two cross fiber with odd
inside parity is exactly one-in/one-out.  The rooted-V exclusion then leaves
three distinct active H positions: two root-cycle positions and one port
position; their `F₂` mass is one.
-/

namespace Erdos85

/-- A two-point fiber whose intersection with a selected shore has binary
parity one consists of a unique inside point and a unique outside point. -/
theorem sizeTwoFiber_exists_unique_inside_outside_of_cast_inter_card_eq_one
    {V : Type*} [DecidableEq V] (fiber shore : Finset V)
    (hcard : fiber.card = 2)
    (hparity : ((fiber ∩ shore).card : ZMod 2) = 1) :
    ∃ xIn xOut,
      fiber ∩ shore = {xIn} ∧ fiber \ shore = {xOut} ∧
        xIn ≠ xOut ∧ fiber = {xIn, xOut} := by
  have hinterLe : (fiber ∩ shore).card ≤ 2 := by
    rw [← hcard]
    exact Finset.card_le_card (Finset.inter_subset_left)
  have hinterZero : (fiber ∩ shore).card ≠ 0 := by
    intro hz
    rw [hz] at hparity
    norm_num at hparity
  have hinterTwo : (fiber ∩ shore).card ≠ 2 := by
    intro hz
    rw [hz] at hparity
    exact (by decide : (2 : ZMod 2) ≠ 1) hparity
  have hinterCard : (fiber ∩ shore).card = 1 := by omega
  obtain ⟨xIn, hxIn⟩ := Finset.card_eq_one.mp hinterCard
  have hdiffCard : (fiber \ shore).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_comm shore fiber, hinterCard, hcard]
  obtain ⟨xOut, hxOut⟩ := Finset.card_eq_one.mp hdiffCard
  have hxInMem : xIn ∈ fiber ∩ shore := by simp [hxIn]
  have hxOutMem : xOut ∈ fiber \ shore := by simp [hxOut]
  have hxInParts := Finset.mem_inter.mp hxInMem
  have hxOutParts := Finset.mem_sdiff.mp hxOutMem
  have hne : xIn ≠ xOut := by
    intro heq
    subst xOut
    exact hxOutParts.2 hxInParts.2
  have hcover : fiber = {xIn, xOut} := by
    ext x
    constructor
    · intro hx
      by_cases hs : x ∈ shore
      · have : x ∈ fiber ∩ shore := Finset.mem_inter.mpr ⟨hx, hs⟩
        rw [hxIn] at this
        simp only [Finset.mem_singleton] at this
        simp [this]
      · have : x ∈ fiber \ shore := Finset.mem_sdiff.mpr ⟨hx, hs⟩
        rw [hxOut] at this
        simp only [Finset.mem_singleton] at this
        simp [this]
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hxInParts.1
      · exact hxOutParts.1
  exact ⟨xIn, xOut, hxIn, hxOut, hne, hcover⟩

/-- The three active positions attached to an exported overlap label. -/
def threeWedgeIndicator {P : Type*} [DecidableEq P]
    (pMinus pPlus pPort : P) (z : P) : ZMod 2 :=
  (if z = pMinus then 1 else 0) +
    (if z = pPlus then 1 else 0) +
      if z = pPort then 1 else 0

/-- With the rooted-V distinctness conditions, the indicator is one exactly
at the two root-cycle positions and the port-crossing position. -/
theorem threeWedgeIndicator_eq_one_iff
    {P : Type*} [DecidableEq P]
    {pMinus pPlus pPort z : P}
    (hmp : pMinus ≠ pPlus) (hmPort : pMinus ≠ pPort)
    (hpPort : pPlus ≠ pPort) :
    threeWedgeIndicator pMinus pPlus pPort z = 1 ↔
      z = pMinus ∨ z = pPlus ∨ z = pPort := by
  unfold threeWedgeIndicator
  by_cases hm : z = pMinus
  · subst z
    simp [hmp, hmPort]
  · by_cases hp : z = pPlus
    · subst z
      simp [hm, hpPort]
    · by_cases hport : z = pPort
      · subst z
        simp [hm, hp]
      · simp [hm, hp, hport]

/-- The exact three-position support has odd total mass
`3 = 1 (mod 2)`, as asserted in `(73rnz_cjibkzzzha)`. -/
theorem threeWedgeIndicator_sum_eq_one
    {P : Type*} [Fintype P] [DecidableEq P]
    (pMinus pPlus pPort : P) :
    (∑ z, threeWedgeIndicator pMinus pPlus pPort z) = 1 := by
  unfold threeWedgeIndicator
  simp_rw [Finset.sum_add_distrib]
  simp
  decide

end Erdos85

#print axioms Erdos85.sizeTwoFiber_exists_unique_inside_outside_of_cast_inter_card_eq_one
#print axioms Erdos85.threeWedgeIndicator_eq_one_iff
#print axioms Erdos85.threeWedgeIndicator_sum_eq_one
