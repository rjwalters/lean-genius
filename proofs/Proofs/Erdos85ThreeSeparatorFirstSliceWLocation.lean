import Proofs.Erdos85ThreeSeparatorFirstSliceInternalProfile
import Proofs.Erdos85ThreeSeparatorExceptionalPointWAttachmentBound

/-!
# Separator location on the first non-endpoint slice

At `a=1`, B16 gives a six-point budget across `K∩X`, `K∩W`, and
`R∩X`.  If the exceptional point lies in `W`, one K-point of `W` is
already used and separator minimality supplies a positive X-attachment.
Parity of `K∩X` then leaves only two or four path endpoints.  This is B23.
-/

open Finset

namespace Erdos85

noncomputable section

/-- Subtraction-free arithmetic core of (B23). -/
theorem firstSlice_W_location_arithmetic
    (kX kW rX m : ℕ)
    (hkXeven : Even kX)
    (hbudget : kX + kW + rX = 6)
    (hkWpos : 1 ≤ kW)
    (hmpos : 1 ≤ m)
    (hmkX : m ≤ kX) :
    (kX = 2 ∨ kX = 4) ∧ rX ≤ 3 ∧ 1 ≤ m ∧ m ≤ kX ∧ kX ≤ 4 := by
  obtain ⟨t, rfl⟩ := hkXeven
  omega

/-- Finset packaging of B23.  The attachment containment is expressed by
`M ⊆ K∩X`, allowing `M` to be instantiated by `N_D(c)∩X`. -/
theorem exceptionalPoint_firstSlice_W_location
    {V : Type*} [DecidableEq V]
    (X W K R M : Finset V) (c : V)
    (hcK : c ∈ K)
    (hcW : c ∈ W)
    (hkXeven : Even (K ∩ X).card)
    (hbudget : (K ∩ X).card + (K ∩ W).card + (R ∩ X).card = 6)
    (hMpos : 1 ≤ M.card)
    (hMKX : M ⊆ K ∩ X) :
    ((K ∩ X).card = 2 ∨ (K ∩ X).card = 4) ∧
      (R ∩ X).card ≤ 3 ∧
      1 ≤ M.card ∧ M.card ≤ (K ∩ X).card ∧ (K ∩ X).card ≤ 4 := by
  have hkWpos : 1 ≤ (K ∩ W).card := by
    have hc : c ∈ K ∩ W := Finset.mem_inter.mpr ⟨hcK, hcW⟩
    exact Finset.one_le_card.mpr ⟨c, hc⟩
  have hmle : M.card ≤ (K ∩ X).card := Finset.card_le_card hMKX
  exact firstSlice_W_location_arithmetic
    (K ∩ X).card (K ∩ W).card (R ∩ X).card M.card
      hkXeven hbudget hkWpos hMpos hmle

end

end Erdos85

#print axioms Erdos85.firstSlice_W_location_arithmetic
#print axioms Erdos85.exceptionalPoint_firstSlice_W_location
