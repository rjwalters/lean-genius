import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic

/-!
# One-in/one-out geometry of an active size-two fiber

An exported third-color overlap has F₂ incidence one in each relevant
two-point cross fiber.  Therefore exactly one endpoint is inside the selected
curl and exactly one is outside.  This is the finite core of
`(73rnz_cjibkzzzg)`.
-/

namespace Erdos85

/-- F₂ incidence one in a two-element fiber forces one selected and one
unselected point. -/
theorem sizeTwoFiber_inter_card_eq_one_and_sdiff_card_eq_one
    {V : Type*} [DecidableEq V]
    (fiber selected : Finset V)
    (hfiber : fiber.card = 2)
    (hparity : ((fiber ∩ selected).card : ZMod 2) = 1) :
    (fiber ∩ selected).card = 1 ∧ (fiber \ selected).card = 1 := by
  have hodd : Odd (fiber ∩ selected).card :=
    ZMod.natCast_eq_one_iff_odd.mp hparity
  have hle : (fiber ∩ selected).card ≤ 2 := by
    rw [← hfiber]
    exact Finset.card_le_card Finset.inter_subset_left
  have hinter : (fiber ∩ selected).card = 1 := by
    rcases hodd with ⟨k, hk⟩
    omega
  have hpartition := Finset.card_inter_add_card_sdiff fiber selected
  constructor
  · exact hinter
  · omega

/-- The two fiber points can therefore be named canonically up to their
unique inside/outside specifications. -/
theorem exists_unique_inside_outside_of_sizeTwoFiber_parity_one
    {V : Type*} [DecidableEq V]
    (fiber selected : Finset V)
    (hfiber : fiber.card = 2)
    (hparity : ((fiber ∩ selected).card : ZMod 2) = 1) :
    ∃ inside outside,
      fiber ∩ selected = {inside} ∧
      fiber \ selected = {outside} ∧
      inside ∈ fiber ∧ inside ∈ selected ∧
      outside ∈ fiber ∧ outside ∉ selected ∧ inside ≠ outside := by
  obtain ⟨hinter, hout⟩ :=
    sizeTwoFiber_inter_card_eq_one_and_sdiff_card_eq_one
      fiber selected hfiber hparity
  obtain ⟨inside, hins⟩ := Finset.card_eq_one.mp hinter
  obtain ⟨outside, houtside⟩ := Finset.card_eq_one.mp hout
  refine ⟨inside, outside, hins, houtside, ?_, ?_, ?_, ?_, ?_⟩
  · have : inside ∈ fiber ∩ selected := by simp [hins]
    exact (Finset.mem_inter.mp this).1
  · have : inside ∈ fiber ∩ selected := by simp [hins]
    exact (Finset.mem_inter.mp this).2
  · have : outside ∈ fiber \ selected := by simp [houtside]
    exact (Finset.mem_sdiff.mp this).1
  · have : outside ∈ fiber \ selected := by simp [houtside]
    exact (Finset.mem_sdiff.mp this).2
  · intro heq
    subst outside
    exact (Finset.mem_sdiff.mp (by simp [houtside] : inside ∈ fiber \ selected)).2
      (Finset.mem_inter.mp (by simp [hins] : inside ∈ fiber ∩ selected)).2

end Erdos85

#print axioms Erdos85.sizeTwoFiber_inter_card_eq_one_and_sdiff_card_eq_one
#print axioms Erdos85.exists_unique_inside_outside_of_sizeTwoFiber_parity_one
