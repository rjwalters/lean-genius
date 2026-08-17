import Mathlib.Logic.Basic

/-! # Deranged non-rainbow three-color normal form -/

namespace Erdos85

/-- Suppose three collision colors exhaust a three-color palette, while the
base color in each position avoids the collision color in that position.
If the base colors are not rainbow, exactly two positions share a base
color; that color is the collision color in the remaining position.

This is the abstract color normal form left by the sharp `λ = 6` near-twin
orbit branch at order sixty four. -/
theorem deranged_nonrainbow_threeColor_normalForm
    {C : Type*} [DecidableEq C]
    {c₁ c₂ c₃ b₁ b₂ b₃ : C}
    (hc₁₂ : c₁ ≠ c₂) (hc₁₃ : c₁ ≠ c₃) (hc₂₃ : c₂ ≠ c₃)
    (hb₁ : b₁ = c₁ ∨ b₁ = c₂ ∨ b₁ = c₃)
    (hb₂ : b₂ = c₁ ∨ b₂ = c₂ ∨ b₂ = c₃)
    (hb₃ : b₃ = c₁ ∨ b₃ = c₂ ∨ b₃ = c₃)
    (havoid₁ : b₁ ≠ c₁) (havoid₂ : b₂ ≠ c₂) (havoid₃ : b₃ ≠ c₃)
    (hnoRainbow : ¬ (b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃)) :
    (b₁ = b₂ ∧ b₃ ≠ b₁ ∧ b₁ = c₃ ∧ (b₃ = c₁ ∨ b₃ = c₂)) ∨
    (b₁ = b₃ ∧ b₂ ≠ b₁ ∧ b₁ = c₂ ∧ (b₂ = c₁ ∨ b₂ = c₃)) ∨
    (b₂ = b₃ ∧ b₁ ≠ b₂ ∧ b₂ = c₁ ∧ (b₁ = c₂ ∨ b₁ = c₃)) := by
  by_cases h₁₂ : b₁ = b₂
  · left
    have hrepeated : b₁ = c₃ := by
      rcases hb₁ with h | h | h
      · exact (havoid₁ h).elim
      · exact (havoid₂ (h₁₂ ▸ h)).elim
      · exact h
    have hremaining : b₃ = c₁ ∨ b₃ = c₂ := by
      rcases hb₃ with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (havoid₃ h).elim
    refine ⟨h₁₂, ?_, hrepeated, hremaining⟩
    rintro h₃₁
    rcases hremaining with h | h
    · exact hc₁₃ (h.symm.trans (h₃₁.trans hrepeated))
    · exact hc₂₃ (h.symm.trans (h₃₁.trans hrepeated))
  by_cases h₁₃ : b₁ = b₃
  · right
    left
    have hrepeated : b₁ = c₂ := by
      rcases hb₁ with h | h | h
      · exact (havoid₁ h).elim
      · exact h
      · exact (havoid₃ (h₁₃ ▸ h)).elim
    have hremaining : b₂ = c₁ ∨ b₂ = c₃ := by
      rcases hb₂ with h | h | h
      · exact Or.inl h
      · exact (havoid₂ h).elim
      · exact Or.inr h
    refine ⟨h₁₃, ?_, hrepeated, hremaining⟩
    rintro h₂₁
    rcases hremaining with h | h
    · exact hc₁₂ (h.symm.trans (h₂₁.trans hrepeated))
    · exact hc₂₃ (hrepeated.symm.trans (h₂₁.symm.trans h))
  by_cases h₂₃ : b₂ = b₃
  · right
    right
    have hrepeated : b₂ = c₁ := by
      rcases hb₂ with h | h | h
      · exact h
      · exact (havoid₂ h).elim
      · exact (havoid₃ (h₂₃ ▸ h)).elim
    have hremaining : b₁ = c₂ ∨ b₁ = c₃ := by
      rcases hb₁ with h | h | h
      · exact (havoid₁ h).elim
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨h₂₃, h₁₂, hrepeated, hremaining⟩
  · exact (hnoRainbow ⟨h₁₂, h₁₃, h₂₃⟩).elim

end Erdos85
