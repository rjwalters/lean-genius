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

/-! ## Relabeling primitives

The graph-facing normalization only has to choose an ordered injection of the
points already used by its first two blocks.  These lemmas extend that partial
labeling to a permutation of all nine high points.  Keeping the extension step
separate avoids making any arbitrary enumeration of the unused high points
part of the eventual theorem statement.
-/

/-- Any ordered list of at most nine distinct high points can be sent to the
same initial segment of `Fin 9` by a permutation. -/
theorem exists_perm_send_to_initialSegment {n : Nat} (hn : n ≤ 9)
    (f : Fin n → Fin 9) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i, σ (f i) = Fin.castLE hn i := by
  exact Equiv.Perm.exists_extending_pair f (Fin.castLE hn) hf
    (Fin.castLE_injective hn)

/-- Relabel six selected distinct points as `0,1,2,3,4,5`.  This is the
extension step for two disjoint triple blocks. -/
theorem exists_perm_normalizing_disjoint_prefix
    (f : Fin 6 → Fin 9) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i, σ (f i) = Fin.castLE (by omega) i :=
  exists_perm_send_to_initialSegment (by omega) f hf

/-- Relabel five selected distinct points as `0,1,2,3,4`.  Ordering the common
point first gives the prefix `012,034` for two triples meeting once. -/
theorem exists_perm_normalizing_intersecting_prefix
    (f : Fin 5 → Fin 9) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i, σ (f i) = Fin.castLE (by omega) i :=
  exists_perm_send_to_initialSegment (by omega) f hf

/-- Mathematical membership criterion for the executable list of triples. -/
theorem mem_allTriples_iff {a b c : Nat} :
    [a, b, c] ∈ allTriples ↔ a < b ∧ b < c ∧ c < 9 := by
  simp [allTriples]
  omega

/-- For triples with distinct entries, the Boolean enumeration test is the
usual statement that their underlying sets meet in at most one point. -/
theorem linB_eq_true_iff_card_inter_le_one
    {a b c d e f : Nat} (hS : List.Nodup [a, b, c]) :
    linB [a, b, c] [d, e, f] = true ↔
      (({a, b, c} : Finset Nat) ∩ {d, e, f}).card ≤ 1 := by
  simp only [linB, Nat.ble_eq]
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (hS.filter _)]
  rw [List.toFinset_filter]
  have heq :
      [a, b, c].toFinset.filter (fun x => [d, e, f].contains x) =
        ({a, b, c} : Finset Nat) ∩ {d, e, f} := by
    ext x
    simp
  rw [heq]

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
