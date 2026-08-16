import Proofs.Erdos85OneHighExchangedPairParity

/-! # Repetition rigidity for four exchanged-label edges -/

namespace Erdos85

noncomputable section

/-- In an even four-edge label multigraph, cancelling two equal edges leaves
an even two-edge multigraph, so the remaining edges are equal as well. -/
theorem remaining_keys_eq_of_four_even_of_first_two_eq
    {L : Type*} [LinearOrder L]
    (p q r s : L × L) (hr : r.1 < r.2) (hs : s.1 < s.2)
    (hpq : p = q)
    (heven : ∀ l, Even
      (unorderedKeyIncidence p l + unorderedKeyIncidence q l +
        unorderedKeyIncidence r l + unorderedKeyIncidence s l)) :
    r = s := by
  subst q
  apply eq_of_two_unorderedKeys_even_incidence r s hr hs
  intro l
  have h := heven l
  by_cases hp : l = p.1 ∨ l = p.2 <;>
    by_cases hr' : l = r.1 ∨ l = r.2 <;>
    by_cases hs' : l = s.1 ∨ l = s.2
  all_goals simp [unorderedKeyIncidence, hp, hr', hs'] at h ⊢
  all_goals norm_num at h

/-- Four nonconstant matching edges with even combined label incidence split
into two repeated canonical miss-pair keys as soon as the first two repeat. -/
theorem remaining_exchangedMissPairKeys_eq_of_four_even_of_first_two_eq
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [LinearOrder L]
    {mate : X → X} {label : X → L} {x₀ x₁ x₂ x₃ : X}
    (_h₀ : x₀ ∈ nonconstantMatchingEdgeSources mate label)
    (_h₁ : x₁ ∈ nonconstantMatchingEdgeSources mate label)
    (h₂ : x₂ ∈ nonconstantMatchingEdgeSources mate label)
    (h₃ : x₃ ∈ nonconstantMatchingEdgeSources mate label)
    (hfirst : exchangedMissPairKey mate label x₀ =
      exchangedMissPairKey mate label x₁)
    (heven : ∀ l, Even
      (unorderedKeyIncidence (exchangedMissPairKey mate label x₀) l +
       unorderedKeyIncidence (exchangedMissPairKey mate label x₁) l +
       unorderedKeyIncidence (exchangedMissPairKey mate label x₂) l +
       unorderedKeyIncidence (exchangedMissPairKey mate label x₃) l)) :
    exchangedMissPairKey mate label x₂ =
      exchangedMissPairKey mate label x₃ := by
  exact remaining_keys_eq_of_four_even_of_first_two_eq _ _ _ _
    (exchangedMissPairKey_lt_of_mem h₂)
    (exchangedMissPairKey_lt_of_mem h₃) hfirst heven

end

end Erdos85
