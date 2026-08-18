import Mathlib

/-!
# Cardinality bridge for the mu-three K-symmetry law

The graph-facing symmetry theorem counts `H \ K`, whereas the executable
enumerator compares `K ∩ H`.  Equal ambient H-fiber sizes make those two
forms equivalent.  This small lemma is the shared arithmetic junction for
both rows and columns.
-/

namespace Erdos85

theorem card_inter_eq_of_card_eq_of_card_sdiff_eq
    {α : Type*} [DecidableEq α]
    (K₁ H₁ K₂ H₂ : Finset α)
    (hH : H₁.card = H₂.card)
    (hdiff : (H₁ \ K₁).card = (H₂ \ K₂).card) :
    (K₁ ∩ H₁).card = (K₂ ∩ H₂).card := by
  have h₁ := Finset.card_inter_add_card_sdiff H₁ K₁
  have h₂ := Finset.card_inter_add_card_sdiff H₂ K₂
  rw [Finset.inter_comm H₁ K₁] at h₁
  rw [Finset.inter_comm H₂ K₂] at h₂
  omega

theorem card_sdiff_eq_of_card_eq_of_card_inter_eq
    {α : Type*} [DecidableEq α]
    (K₁ H₁ K₂ H₂ : Finset α)
    (hH : H₁.card = H₂.card)
    (hinter : (K₁ ∩ H₁).card = (K₂ ∩ H₂).card) :
    (H₁ \ K₁).card = (H₂ \ K₂).card := by
  have h₁ := Finset.card_inter_add_card_sdiff H₁ K₁
  have h₂ := Finset.card_inter_add_card_sdiff H₂ K₂
  rw [Finset.inter_comm H₁ K₁] at h₁
  rw [Finset.inter_comm H₂ K₂] at h₂
  omega

end Erdos85

#print axioms Erdos85.card_inter_eq_of_card_eq_of_card_sdiff_eq
#print axioms Erdos85.card_sdiff_eq_of_card_eq_of_card_inter_eq
