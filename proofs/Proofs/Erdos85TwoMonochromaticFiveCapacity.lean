import Mathlib

/-!
# Two monochromatic five-sets versus capacities 7,4,4

This is the final pigeonhole step in the all-triangle-free `C10 + C6`
fiber-margin obstruction.
-/

namespace Erdos85

/-- Two disjoint monochromatic five-sets cannot be colored with three colors
when one color class has capacity seven and each other class capacity four. -/
theorem false_of_two_disjoint_monochromatic_five_of_capacities
    {V : Type*} [Fintype V] [DecidableEq V]
    (color : V → Fin 3) (large : Fin 3)
    (S T : Finset V) (α β : Fin 3)
    (hdisj : Disjoint S T)
    (hScard : S.card = 5) (hTcard : T.card = 5)
    (hSmono : ∀ x ∈ S, color x = α)
    (hTmono : ∀ x ∈ T, color x = β)
    (hcap : ∀ c : Fin 3,
      ((Finset.univ : Finset V).filter fun x => color x = c).card ≤
        if c = large then 7 else 4) : False := by
  classical
  let fiber (c : Fin 3) :=
    (Finset.univ : Finset V).filter fun x => color x = c
  have hSsub : S ⊆ fiber α := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSmono x hx⟩
  have hTsub : T ⊆ fiber β := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTmono x hx⟩
  by_cases hab : α = β
  · subst β
    have hunionSub : S ∪ T ⊆ fiber α := Finset.union_subset hSsub hTsub
    have hunionCard : (S ∪ T).card = 10 := by
      rw [Finset.card_union_of_disjoint hdisj, hScard, hTcard]
    have hle := Finset.card_le_card hunionSub
    have hc := hcap α
    simp only [fiber] at hle
    split at hc <;> omega
  · have hsmall : α ≠ large ∨ β ≠ large := by
      by_contra h
      push_neg at h
      exact hab (h.1.trans h.2.symm)
    rcases hsmall with hα | hβ
    · have hle := Finset.card_le_card hSsub
      have hc := hcap α
      simp [fiber, hα, hScard] at hle hc
      omega
    · have hle := Finset.card_le_card hTsub
      have hc := hcap β
      simp [fiber, hβ, hTcard] at hle hc
      omega

/-- Ambient-finset form of the same capacity contradiction. -/
theorem false_of_two_disjoint_monochromatic_five_in_of_capacities
    {V : Type*} [DecidableEq V]
    (color : V → Fin 3) (large : Fin 3) (U S T : Finset V) (α β : Fin 3)
    (hSU : S ⊆ U) (hTU : T ⊆ U)
    (hdisj : Disjoint S T)
    (hScard : S.card = 5) (hTcard : T.card = 5)
    (hSmono : ∀ x ∈ S, color x = α)
    (hTmono : ∀ x ∈ T, color x = β)
    (hcap : ∀ c : Fin 3,
      (U.filter fun x => color x = c).card ≤
        if c = large then 7 else 4) : False := by
  classical
  let fiber (c : Fin 3) := U.filter fun x => color x = c
  have hSsub : S ⊆ fiber α := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSU hx, hSmono x hx⟩
  have hTsub : T ⊆ fiber β := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hTU hx, hTmono x hx⟩
  by_cases hab : α = β
  · subst β
    have hunionSub : S ∪ T ⊆ fiber α := Finset.union_subset hSsub hTsub
    have hunionCard : (S ∪ T).card = 10 := by
      rw [Finset.card_union_of_disjoint hdisj, hScard, hTcard]
    have hle := Finset.card_le_card hunionSub
    have hc := hcap α
    simp only [fiber] at hle
    split at hc <;> omega
  · have hsmall : α ≠ large ∨ β ≠ large := by
      by_contra h
      push_neg at h
      exact hab (h.1.trans h.2.symm)
    rcases hsmall with hα | hβ
    · have hle := Finset.card_le_card hSsub
      have hc := hcap α
      simp [fiber, hα, hScard] at hle hc
      omega
    · have hle := Finset.card_le_card hTsub
      have hc := hcap β
      simp [fiber, hβ, hTcard] at hle hc
      omega

end Erdos85

#print axioms Erdos85.false_of_two_disjoint_monochromatic_five_of_capacities
