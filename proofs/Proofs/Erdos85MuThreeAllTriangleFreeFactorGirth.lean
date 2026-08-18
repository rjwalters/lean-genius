import Proofs.Erdos85MuThreeAllTriangleFreeResidualRowBlocks

/-!
# The all-triangle-free factor has no four-cycle

The twin-row pigeonhole obstruction is translated here into the statement
that the auxiliary two-regular bipartite relation `H` cannot contain a
`K₂,₂`.  In the graph-facing application this is redundant with ambient
C4-freeness.  It does **not** exclude a `[2]` part of the defect-component
partition: such a part denotes a size-two normalized defect component, not
a four-cycle of `H`.
-/

open SimpleGraph

namespace Erdos85

private theorem eq_or_eq_of_mem_card_two
    {α : Type*} [DecidableEq α] {s : Finset α} {a b z : α}
    (hcard : s.card = 2) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hz : z ∈ s) : z = a ∨ z = b := by
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hcard
  rw [hs] at ha hb hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hz
  rcases hz with rfl | rfl
  · rcases ha with rfl | rfl
    · exact Or.inl rfl
    · rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact Or.inr rfl
  · rcases ha with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- In the all-triangle-free mixed grid (`K = H`), the auxiliary
two-regular relation contains no four-cycle. -/
theorem MuThreeMixedGridCode.no_factor_fourCycle
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H : X → Y → Prop) [DecidableRel H]
    (C : SimpleGraph (muThreeMixedCell H)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H H C) :
    ¬ ∃ x x' y y', x ≠ x' ∧ y ≠ y' ∧
      H x y ∧ H x y' ∧ H x' y ∧ H x' y' := by
  rintro ⟨x, x', y, y', hxx', hyy', hxy, hxy', hx'y, hx'y'⟩
  apply code.no_distinct_twin_rows H C hxx'
  intro z
  constructor
  · intro hxz
    let Nx := (Finset.univ : Finset Y).filter fun w => H x w
    have hy : y ∈ Nx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    have hy' : y' ∈ Nx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy'⟩
    have hz : z ∈ Nx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩
    rcases eq_or_eq_of_mem_card_two (code.H_twoRegular.1 x) hy hy' hyy' hz with
      rfl | rfl
    · exact hx'y
    · exact hx'y'
  · intro hx'z
    let Nx' := (Finset.univ : Finset Y).filter fun w => H x' w
    have hy : y ∈ Nx' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'y⟩
    have hy' : y' ∈ Nx' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'y'⟩
    have hz : z ∈ Nx' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'z⟩
    rcases eq_or_eq_of_mem_card_two (code.H_twoRegular.1 x') hy hy' hyy' hz with
      rfl | rfl
    · exact hxy
    · exact hxy'

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.no_factor_fourCycle
