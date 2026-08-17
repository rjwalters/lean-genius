import Proofs.Erdos85DegreeTwoNoTripleRowCollision

/-! # Colored triangle collision terminal -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If every edge of a three-vertex triangle is a row collision in its
assigned two-regular factor, the three colors must be pairwise distinct.
Equivalently, the no-rainbow color alternative is impossible. -/
theorem false_of_degreeTwo_coloredTriangle_collisions_noRainbow
    {V C : Type*} [Fintype V] [DecidableEq V]
    (O : C → SimpleGraph V) [hdec : ∀ c, DecidableRel (O c).Adj]
    (hdeg : ∀ c z, (O c).degree z = 2)
    {a b c : V} (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c)
    {α β γ : C}
    (hab : ∀ z : V, (O α).adjMatrix ℤ a z = (O α).adjMatrix ℤ b z)
    (hac : ∀ z : V, (O β).adjMatrix ℤ a z = (O β).adjMatrix ℤ c z)
    (hbc : ∀ z : V, (O γ).adjMatrix ℤ b z = (O γ).adjMatrix ℤ c z)
    (hnoRainbow : α = β ∨ α = γ ∨ β = γ) : False := by
  rcases hnoRainbow with hαβ | hαγ | hβγ
  · subst β
    exact degreeTwo_not_three_distinct_adjMatrix_rows_eq
      (O α) (hdeg α) habne hacne hbcne hab hac
  · subst γ
    have hac' : ∀ z : V,
        (O α).adjMatrix ℤ a z = (O α).adjMatrix ℤ c z := by
      intro z
      exact (hab z).trans (hbc z)
    exact degreeTwo_not_three_distinct_adjMatrix_rows_eq
      (O α) (hdeg α) habne hacne hbcne hab hac'
  · subst γ
    have hab' : ∀ z : V,
        (O β).adjMatrix ℤ a z = (O β).adjMatrix ℤ b z := by
      intro z
      exact (hac z).trans (hbc z).symm
    exact degreeTwo_not_three_distinct_adjMatrix_rows_eq
      (O β) (hdeg β) habne hacne hbcne hab' hac

/-- Contrapositive interface: three pairwise edge collisions in a family of
two-factors force a rainbow of collision colors. -/
theorem degreeTwo_coloredTriangle_collisions_pairwiseDistinct
    {V C : Type*} [Fintype V] [DecidableEq V]
    (O : C → SimpleGraph V) [hdec : ∀ c, DecidableRel (O c).Adj]
    (hdeg : ∀ c z, (O c).degree z = 2)
    {a b c : V} (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c)
    {α β γ : C}
    (hab : ∀ z : V, (O α).adjMatrix ℤ a z = (O α).adjMatrix ℤ b z)
    (hac : ∀ z : V, (O β).adjMatrix ℤ a z = (O β).adjMatrix ℤ c z)
    (hbc : ∀ z : V, (O γ).adjMatrix ℤ b z = (O γ).adjMatrix ℤ c z) :
    α ≠ β ∧ α ≠ γ ∧ β ≠ γ := by
  constructor
  · intro h
    exact false_of_degreeTwo_coloredTriangle_collisions_noRainbow
      O hdeg habne hacne hbcne hab hac hbc (Or.inl h)
  constructor
  · intro h
    exact false_of_degreeTwo_coloredTriangle_collisions_noRainbow
      O hdeg habne hacne hbcne hab hac hbc (Or.inr (Or.inl h))
  · intro h
    exact false_of_degreeTwo_coloredTriangle_collisions_noRainbow
      O hdeg habne hacne hbcne hab hac hbc (Or.inr (Or.inr h))

end

end Erdos85
