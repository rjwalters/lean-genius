import Proofs.Erdos85OneHighAllEvenCapacityInventory

/-! # Index-based residual adapter for the H1 all-even inventory -/

namespace Erdos85

/-- Select inventory rows by numeric indices, silently ignoring out-of-range
indices.  This avoids requiring executable equality on function-valued miss
tables. -/
def oneHighTablesAtIndices {α : Type*}
    (inventory : List α) (indices : List Nat) : List α :=
  indices.filterMap fun index => inventory[index]?

/-- The ordered complement of a list of known indices in an inventory. -/
def oneHighResidualIndices {α : Type*}
    (inventory : List α) (known : List Nat) : List Nat :=
  (List.range inventory.length).filter fun index => !known.contains index

theorem oneHigh_mem_tablesAtIndices_of_mem
    {α : Type*} {inventory : List α} {indices : List Nat}
    {index : Nat} (hindex : index ∈ indices)
    (hbound : index < inventory.length) :
    inventory[index] ∈ oneHighTablesAtIndices inventory indices := by
  unfold oneHighTablesAtIndices
  apply List.mem_filterMap.mpr
  exact ⟨index, hindex, by simp [hbound]⟩

theorem oneHigh_mem_known_or_residual_tables
    {α : Type*} (inventory : List α) (known : List Nat)
    {table : α} (htable : table ∈ inventory) :
    table ∈ oneHighTablesAtIndices inventory known ∨
      table ∈ oneHighTablesAtIndices inventory
        (oneHighResidualIndices inventory known) := by
  obtain ⟨index, hbound, hget⟩ := List.mem_iff_getElem.mp htable
  subst table
  by_cases hknown : index ∈ known
  · exact Or.inl (oneHigh_mem_tablesAtIndices_of_mem hknown hbound)
  · apply Or.inr
    apply oneHigh_mem_tablesAtIndices_of_mem
    simp [oneHighResidualIndices, hbound, hknown]

/-- If a checked bank covers the selected indices and the complementary
indices are checked separately, every inventory row is checked. -/
theorem oneHigh_checked_of_index_bank_and_residual
    {α : Type*} {Checked : α → Prop}
    (inventory : List α) (known : List Nat)
    (hknown : ∀ table ∈ oneHighTablesAtIndices inventory known, Checked table)
    (hresidual : ∀ table ∈ oneHighTablesAtIndices inventory
      (oneHighResidualIndices inventory known), Checked table) :
    ∀ table ∈ inventory, Checked table := by
  intro table htable
  rcases oneHigh_mem_known_or_residual_tables inventory known htable with
    hmem | hmem
  · exact hknown table hmem
  · exact hresidual table hmem

end Erdos85
