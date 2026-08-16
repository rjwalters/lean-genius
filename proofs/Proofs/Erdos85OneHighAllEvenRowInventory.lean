import Proofs.Erdos85OneHighGraphPairingRefinement
import Proofs.Erdos85OneHighV2CapacityInventory

/-! # Reciprocal singleton-row pruning of the one-high inventory -/

namespace Erdos85

private theorem ofFn_id_any_eq_true_iff {n : Nat} (p : Fin n → Bool) :
    (List.ofFn fun i : Fin n => i).any p = true ↔
      ∃ i : Fin n, p i = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hp⟩
    rw [List.mem_ofFn] at hi
    obtain ⟨j, rfl⟩ := hi
    exact ⟨j, hp⟩
  · rintro ⟨i, hp⟩
    refine ⟨i, ?_, hp⟩
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩

/-- Some diagonal singleton occurs in the compatible pairing space of the
canonical source-zero row.  This is the executable table signature forced by
the positive-profile reciprocal same-miss configuration. -/
def oneHighTableHasSourceZeroDiagonalSingleton
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  (List.ofFn fun label : Fin 8 => label).any fun label =>
    decide ([(label, label)] ∈
      oneHighCompatibleSourcePairings profile table 0)

theorem oneHighTableHasSourceZeroDiagonalSingleton_of_mem
    {profile : Nat} {table : OneHighMissTable} {label : Fin 8}
    (hmem : [(label, label)] ∈
      oneHighCompatibleSourcePairings profile table 0) :
    oneHighTableHasSourceZeroDiagonalSingleton profile table = true := by
  rw [oneHighTableHasSourceZeroDiagonalSingleton,
    ofFn_id_any_eq_true_iff]
  exact ⟨label, by simpa using hmem⟩

theorem oneHighTableHasSourceZeroDiagonalSingleton_sound
    {profile : Nat} {table : OneHighMissTable}
    (h : oneHighTableHasSourceZeroDiagonalSingleton profile table = true) :
    ∃ label : Fin 8, [(label, label)] ∈
      oneHighCompatibleSourcePairings profile table 0 := by
  rw [oneHighTableHasSourceZeroDiagonalSingleton,
    ofFn_id_any_eq_true_iff] at h
  rcases h with ⟨label, hlabel⟩
  exact ⟨label, of_decide_eq_true hlabel⟩

/-- Capacity-admissible inventory rows retaining the exact reciprocal
singleton-row signature. -/
def oneHighReciprocalSingletonRowInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasSourceZeroDiagonalSingleton profile.val)

theorem oneHighReciprocalSingletonRowInventoryTables_length_zero :
    (oneHighReciprocalSingletonRowInventoryTables 0).length = 0 := by
  native_decide

theorem oneHighReciprocalSingletonRowInventoryTables_length_one :
    (oneHighReciprocalSingletonRowInventoryTables 1).length = 867 := by
  native_decide

theorem oneHighReciprocalSingletonRowInventoryTables_length_two :
    (oneHighReciprocalSingletonRowInventoryTables 2).length = 1623 := by
  native_decide

theorem oneHighReciprocalSingletonRowInventoryTables_length_three :
    (oneHighReciprocalSingletonRowInventoryTables 3).length = 1076 := by
  native_decide

theorem oneHighReciprocalSingletonRowInventoryTables_length_four :
    (oneHighReciprocalSingletonRowInventoryTables 4).length = 453 := by
  native_decide

/-- Exact size of the capacity-plus-reciprocal-singleton residual. -/
theorem oneHighReciprocalSingletonRowInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighReciprocalSingletonRowInventoryTables profile).length).sum =
        4019 := by
  native_decide

/-- Across the positive profiles where the reciprocal theorem applies, the
singleton row removes 7,847 capacity-admissible orbit representatives. -/
theorem oneHighReciprocalSingletonRowInventory_positive_removed_count :
    ((List.finRange 4).map fun offset =>
      (oneHighCapacityInventoryTables ⟨offset.val + 1, by omega⟩).length).sum -
      ((List.finRange 4).map fun offset =>
        (oneHighReciprocalSingletonRowInventoryTables
          ⟨offset.val + 1, by omega⟩).length).sum = 7847 := by
  native_decide

end Erdos85
