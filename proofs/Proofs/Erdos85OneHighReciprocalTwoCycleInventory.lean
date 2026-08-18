import Proofs.Erdos85OneHighAllEvenRowInventory

/-! # Reciprocal diagonal two-cycle pruning of the one-high inventory -/

namespace Erdos85

/-- The exact executable signature of a reciprocal diagonal two-cycle:
the canonical source-zero row is the singleton diagonal at a one-edge label
`u`, and the source-`u` row is the singleton diagonal back at zero. -/
def oneHighTableHasReciprocalDiagonalTwoCycle
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  (List.ofFn fun label : Fin 8 => label).any fun label =>
    decide (oneHighFamilyInternalEdges profile label = 1 ∧
      [(label, label)] ∈ oneHighCompatibleSourcePairings profile table 0 ∧
      [((0 : Fin 8), (0 : Fin 8))] ∈
        oneHighCompatibleSourcePairings profile table label)

theorem oneHighTableHasReciprocalDiagonalTwoCycle_of_mem
    {profile : Nat} {table : OneHighMissTable} {label : Fin 8}
    (hedge : oneHighFamilyInternalEdges profile label = 1)
    (hforward : [(label, label)] ∈
      oneHighCompatibleSourcePairings profile table 0)
    (hreverse : [((0 : Fin 8), (0 : Fin 8))] ∈
      oneHighCompatibleSourcePairings profile table label) :
    oneHighTableHasReciprocalDiagonalTwoCycle profile table = true := by
  rw [oneHighTableHasReciprocalDiagonalTwoCycle, List.any_eq_true]
  refine ⟨label, ?_, ?_⟩
  · rw [List.mem_ofFn]
    exact ⟨label, rfl⟩
  · simp [hedge, hforward, hreverse]

/-- Capacity-admissible rows retaining the reciprocal diagonal two-cycle. -/
def oneHighReciprocalDiagonalTwoCycleInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasReciprocalDiagonalTwoCycle profile.val)

theorem oneHighReciprocalDiagonalTwoCycleInventoryTables_length_zero :
    (oneHighReciprocalDiagonalTwoCycleInventoryTables 0).length = 0 := by
  native_decide

theorem oneHighReciprocalDiagonalTwoCycleInventoryTables_length_one :
    (oneHighReciprocalDiagonalTwoCycleInventoryTables 1).length = 0 := by
  native_decide

/-- The profile-2 reciprocal-diagonal left arm has only 78 surviving orbit
representatives, versus 4,717 capacity rows and 1,623 one-sided singleton
rows. -/
theorem oneHighReciprocalDiagonalTwoCycleInventoryTables_length_two :
    (oneHighReciprocalDiagonalTwoCycleInventoryTables 2).length = 78 := by
  native_decide

theorem oneHighReciprocalDiagonalTwoCycleInventoryTables_length_three :
    (oneHighReciprocalDiagonalTwoCycleInventoryTables 3).length = 9 := by
  native_decide

theorem oneHighReciprocalDiagonalTwoCycleInventoryTables_length_four :
    (oneHighReciprocalDiagonalTwoCycleInventoryTables 4).length = 46 := by
  native_decide

theorem oneHighReciprocalDiagonalTwoCycleInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighReciprocalDiagonalTwoCycleInventoryTables profile).length).sum =
        133 := by
  native_decide

end Erdos85
