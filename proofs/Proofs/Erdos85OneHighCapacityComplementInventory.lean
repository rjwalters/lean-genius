import Proofs.Erdos85OneHighAllEvenCapacityInventory

/-! # Complement of the one-high all-even capacity inventory

This file names the exact part of the 13,351-row capacity inventory left after
the 2,503 rows admitting an all-even restricted pairing refinement are removed.
The resulting 10,848 rows are the certificate queue for the complementary H1
branch.
-/

namespace Erdos85

noncomputable section

/-- Capacity-compatible rows which do not admit an all-even restricted pairing
refinement. -/
def oneHighNonAllEvenCapacityInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter fun table =>
    !(oneHighTableHasAllEvenPairingRestricted profile.val table)

/-- Exact complementary census, in profiles `0,1,2,3,4`. -/
theorem oneHighNonAllEvenCapacityInventoryTables_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighNonAllEvenCapacityInventoryTables profile).length) =
        [876, 3601, 3130, 2687, 554] := by
  native_decide

/-- The complement contains exactly 10,848 capacity rows. -/
theorem oneHighNonAllEvenCapacityInventoryTables_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighNonAllEvenCapacityInventoryTables profile).length).sum = 10848 := by
  rw [oneHighNonAllEvenCapacityInventoryTables_lengths]
  decide

/-- Every capacity row lies in exactly one of the all-even inventory and its
complement.  This is the membership-level partition used by the two certificate
banks. -/
theorem oneHighCapacityInventory_mem_iff_allEven_or_nonAllEven
    {profile : Fin 5} {table : OneHighMissTable} :
    table ∈ oneHighCapacityInventoryTables profile ↔
      table ∈ oneHighAllEvenCapacityInventoryTables profile ∨
      table ∈ oneHighNonAllEvenCapacityInventoryTables profile := by
  simp only [oneHighAllEvenCapacityInventoryTables,
    oneHighNonAllEvenCapacityInventoryTables, List.mem_filter]
  constructor
  · intro hcapacity
    by_cases heven :
        oneHighTableHasAllEvenPairingRestricted profile.val table = true
    · exact Or.inl ⟨hcapacity, heven⟩
    · right
      refine ⟨hcapacity, ?_⟩
      simp [heven]
  · rintro (⟨hcapacity, _⟩ | ⟨hcapacity, _⟩) <;> exact hcapacity

/-- The two sides of the capacity partition are disjoint. -/
theorem oneHighAllEvenCapacityInventory_disjoint_nonAllEven
    (profile : Fin 5) :
    List.Disjoint
      (oneHighAllEvenCapacityInventoryTables profile)
      (oneHighNonAllEvenCapacityInventoryTables profile) := by
  rw [List.disjoint_left]
  intro table hall hnon
  simp only [oneHighAllEvenCapacityInventoryTables, List.mem_filter] at hall
  simp only [oneHighNonAllEvenCapacityInventoryTables, List.mem_filter] at hnon
  rcases hall with ⟨_, heven⟩
  rcases hnon with ⟨_, hnotEven⟩
  simp [heven] at hnotEven

/-- Membership in the complementary inventory exposes the failed executable
all-even-refinement predicate. -/
theorem oneHighTableHasAllEvenPairingRestricted_eq_false_of_mem_nonAllEven
    {profile : Fin 5} {table : OneHighMissTable}
    (hmem : table ∈ oneHighNonAllEvenCapacityInventoryTables profile) :
    oneHighTableHasAllEvenPairingRestricted profile.val table = false := by
  simp only [oneHighNonAllEvenCapacityInventoryTables, List.mem_filter] at hmem
  rcases hmem with ⟨_, hnotEven⟩
  simpa using hnotEven

end

end Erdos85
