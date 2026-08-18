import Mathlib.Data.Finset.Card

/-! # Saturation inside a three-element fiber

The `[3,3]` residual-defect propagation repeatedly uses one elementary step:
a confined two-element neighborhood inside a three-element color fiber is
completely determined as soon as one excluded cell is known.
-/

namespace Erdos85

theorem two_subset_three_eq_erase_of_not_mem
    {α : Type*} [DecidableEq α]
    (S T : Finset α) (z : α)
    (hsub : S ⊆ T) (hS : S.card = 2) (hT : T.card = 3)
    (hzT : z ∈ T) (hzS : z ∉ S) :
    S = T.erase z := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxz => hzS (hxz ▸ hx), hsub hx⟩
  · rw [Finset.card_erase_of_mem hzT, hS, hT]

/-- Membership form of three-fiber saturation. -/
theorem mem_twoFiber_iff_mem_threeFiber_and_ne_excluded
    {α : Type*} [DecidableEq α]
    (S T : Finset α) (z x : α)
    (hsub : S ⊆ T) (hS : S.card = 2) (hT : T.card = 3)
    (hzT : z ∈ T) (hzS : z ∉ S) :
    x ∈ S ↔ x ∈ T ∧ x ≠ z := by
  rw [two_subset_three_eq_erase_of_not_mem S T z hsub hS hT hzT hzS]
  simp [and_comm]

/-- Every non-excluded member of the three-fiber is forced into the
two-element neighborhood. -/
theorem mem_twoFiber_of_mem_threeFiber_of_ne_excluded
    {α : Type*} [DecidableEq α]
    (S T : Finset α) (z x : α)
    (hsub : S ⊆ T) (hS : S.card = 2) (hT : T.card = 3)
    (hzT : z ∈ T) (hzS : z ∉ S)
    (hxT : x ∈ T) (hxz : x ≠ z) :
    x ∈ S :=
  (mem_twoFiber_iff_mem_threeFiber_and_ne_excluded
    S T z x hsub hS hT hzT hzS).2 ⟨hxT, hxz⟩

/-- Predicate/filter form used directly by confined graph neighborhoods. -/
theorem filter_eq_erase_of_card_two_of_confined_in_card_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (z : α)
    (hconfined : ∀ x, P x → Q x)
    (hP : ((Finset.univ : Finset α).filter P).card = 2)
    (hQ : ((Finset.univ : Finset α).filter Q).card = 3)
    (hzQ : Q z) (hzP : ¬ P z) :
    (Finset.univ : Finset α).filter P =
      ((Finset.univ : Finset α).filter Q).erase z := by
  apply two_subset_three_eq_erase_of_not_mem
  · intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, hconfined x (Finset.mem_filter.mp hx).2⟩
  · exact hP
  · exact hQ
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hzQ⟩
  · simpa using hzP

end Erdos85

#print axioms Erdos85.two_subset_three_eq_erase_of_not_mem
#print axioms Erdos85.filter_eq_erase_of_card_two_of_confined_in_card_three
