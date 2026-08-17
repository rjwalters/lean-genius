import Mathlib

/-! # A two-regular graph has no triple row collision -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Three pairwise distinct vertices of a two-regular simple graph cannot
have the same neighborhood row. -/
theorem degreeTwo_not_three_distinct_neighborFinset_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z = 2)
    {a b c : V} (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c)
    (hab : H.neighborFinset a = H.neighborFinset b)
    (hac : H.neighborFinset a = H.neighborFinset c) : False := by
  have hNa : (H.neighborFinset a).card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hdeg a]
  have hnonempty : (H.neighborFinset a).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨r, hra⟩ := hnonempty
  have har : H.Adj a r := (H.mem_neighborFinset a r).mp hra
  have hbr : H.Adj b r := by
    apply (H.mem_neighborFinset b r).mp
    rw [← hab]
    exact hra
  have hcr : H.Adj c r := by
    apply (H.mem_neighborFinset c r).mp
    rw [← hac]
    exact hra
  have hsub : ({a, b, c} : Finset V) ⊆ H.neighborFinset r := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact (H.mem_neighborFinset r _).mpr har.symm
    · exact (H.mem_neighborFinset r _).mpr hbr.symm
    · exact (H.mem_neighborFinset r _).mpr hcr.symm
  have hle := Finset.card_le_card hsub
  have htriple : ({a, b, c} : Finset V).card = 3 := by
    simp [habne, hacne, hbcne]
  have hNr : (H.neighborFinset r).card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hdeg r]
  omega

/-- Integral adjacency-row form, matching the output of commuting collision
propagation. -/
theorem degreeTwo_not_three_distinct_adjMatrix_rows_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z = 2)
    {a b c : V} (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c)
    (hab : ∀ z : V, H.adjMatrix ℤ a z = H.adjMatrix ℤ b z)
    (hac : ∀ z : V, H.adjMatrix ℤ a z = H.adjMatrix ℤ c z) : False := by
  have hNab : H.neighborFinset a = H.neighborFinset b := by
    ext z
    rw [H.mem_neighborFinset, H.mem_neighborFinset]
    have h := hab z
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply] at h
    by_cases haz : H.Adj a z <;> by_cases hbz : H.Adj b z <;> simp_all
  have hNac : H.neighborFinset a = H.neighborFinset c := by
    ext z
    rw [H.mem_neighborFinset, H.mem_neighborFinset]
    have h := hac z
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply] at h
    by_cases haz : H.Adj a z <;> by_cases hcz : H.Adj c z <;> simp_all
  exact degreeTwo_not_three_distinct_neighborFinset_eq
    H hdeg habne hacne hbcne hNab hNac

end

end Erdos85
