import Proofs.Erdos85OrderFortyNineTableVerification

/-!
# Interface for prefix-normalizing the order-49 triple systems

The finite enumeration is deliberately separated from the graph-labeling
argument.  This file characterizes membership in the three raw enumerations
by the small collection of mathematical conditions that a relabeling must
establish: the fixed first block, one of the two possible second blocks,
strict lexicographic order, and pairwise linearity.
-/

namespace Erdos85
namespace OrderFortyNineWitnessTable

def firstTriple : List Nat := [0, 1, 2]

theorem mem_rawT2_iff {T2 : List Nat} :
    [firstTriple, T2] ∈ rawT2 ↔ T2 ∈ secondTriples := by
  simp [rawT2, firstTriple]

theorem mem_rawT3_iff {T2 T3 : List Nat} :
    [firstTriple, T2, T3] ∈ rawT3 ↔
      T2 ∈ secondTriples ∧
      T3 ∈ allTriples ∧
      encTriple T2 < encTriple T3 ∧
      linB T3 firstTriple = true ∧ linB T3 T2 = true := by
  simp [rawT3, firstTriple, Bool.and_eq_true, Nat.ble_eq]

theorem mem_rawT4_iff {T2 T3 T4 : List Nat} :
    [firstTriple, T2, T3, T4] ∈ rawT4 ↔
      T2 ∈ secondTriples ∧
      T3 ∈ allTriples ∧ T4 ∈ allTriples ∧
      encTriple T2 < encTriple T3 ∧
      encTriple T3 < encTriple T4 ∧
      linB T3 firstTriple = true ∧ linB T3 T2 = true ∧
      linB T4 firstTriple = true ∧ linB T4 T2 = true ∧
      linB T4 T3 = true := by
  simp [rawT4, firstTriple, Bool.and_eq_true, Nat.ble_eq] <;> tauto

theorem exists_tableT2_row_of_mem_rawT2
    {S : List (List Nat)} (hS : S ∈ rawT2) :
    ∃ row ∈ tableT2, row.1 = S := by
  have hmap : S ∈ tableT2.map (·.1) := by
    rw [← rawT2_eq_table]
    exact hS
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hmap
  exact ⟨row, hrow, heq⟩

theorem exists_tableT3_row_of_mem_rawT3
    {S : List (List Nat)} (hS : S ∈ rawT3) :
    ∃ row ∈ tableT3, row.1 = S := by
  have hmap : S ∈ tableT3.map (·.1) := by
    rw [← rawT3_eq_table]
    exact hS
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hmap
  exact ⟨row, hrow, heq⟩

theorem exists_tableT4_row_of_mem_rawT4
    {S : List (List Nat)} (hS : S ∈ rawT4) :
    ∃ row ∈ tableT4, row.1 = S := by
  have hmap : S ∈ tableT4.map (·.1) := by
    rw [← rawT4_eq_table]
    exact hS
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hmap
  exact ⟨row, hrow, heq⟩

end OrderFortyNineWitnessTable
end Erdos85
