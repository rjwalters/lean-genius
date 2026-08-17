import Proofs.Erdos85OneHighAllEvenRowInventory
import Proofs.Erdos85OneHighKnownSectorParity

/-! # All-even reciprocal-singleton inventory intersection -/

namespace Erdos85

/-- Some compatible graph pairing has even multiplicity on every
off-diagonal key, expressed through the compact reachable parity states. -/
def oneHighTableHasAllEvenPairing
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  (oneHighPairingParityStates profile table).any
    oneHighParityMaskAllOffDiagonalEven

/-- Any explicit compatible all-even refinement supplies the compact table
predicate. -/
theorem oneHighTableHasAllEvenPairing_of_refinement
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈ oneHighPairingRefinements profile table)
    (heven : oneHighRefinementAllOffDiagonalEven refinement = true) :
    oneHighTableHasAllEvenPairing profile table = true := by
  rw [oneHighTableHasAllEvenPairing, List.any_eq_true]
  refine ⟨oneHighPairingRefinementParityMask refinement, ?_, ?_⟩
  · exact (mem_oneHighPairingParityStates_iff profile table _).2
      ⟨refinement, hrefinement, rfl⟩
  · rwa [oneHighParityMaskAllOffDiagonalEven_refinement]

/-- Capacity-admissible reciprocal-singleton rows retaining at least one
reachable all-even pairing state. -/
def oneHighAllEvenSingletonInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighReciprocalSingletonRowInventoryTables profile).filter
    (oneHighTableHasAllEvenPairing profile.val)

theorem oneHighAllEvenSingletonInventoryTables_length_zero :
    (oneHighAllEvenSingletonInventoryTables 0).length = 0 := by
  native_decide

theorem oneHighAllEvenSingletonInventoryTables_length_one :
    (oneHighAllEvenSingletonInventoryTables 1).length = 5 := by
  native_decide

theorem oneHighAllEvenSingletonInventoryTables_length_two :
    (oneHighAllEvenSingletonInventoryTables 2).length = 790 := by
  native_decide

theorem oneHighAllEvenSingletonInventoryTables_length_three :
    (oneHighAllEvenSingletonInventoryTables 3).length = 4 := by
  native_decide

theorem oneHighAllEvenSingletonInventoryTables_length_four :
    (oneHighAllEvenSingletonInventoryTables 4).length = 200 := by
  native_decide

theorem oneHighAllEvenSingletonInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighAllEvenSingletonInventoryTables profile).length).sum = 999 := by
  native_decide

/-- The all-even parity requirement removes another 3,020 of the 4,019
reciprocal-singleton capacity rows. -/
theorem oneHighAllEvenSingletonInventory_removed_count :
    ((List.finRange 5).map fun profile =>
      (oneHighReciprocalSingletonRowInventoryTables profile).length).sum -
      ((List.finRange 5).map fun profile =>
        (oneHighAllEvenSingletonInventoryTables profile).length).sum = 3020 := by
  native_decide

/-! ## Profile-two reciprocal diagonal cycle

The first arm of the profile-two graph dichotomy fixes the reciprocal label
to label `2`: source zero has the singleton row `[(2, 2)]`, while source two
has the reverse singleton row `[(0, 0)]`.  Keep this signature executable so
the graph bridge can hand it directly to the finite inventory.
-/

def oneHighTableHasProfileTwoReciprocalDiagonalCycle
    (table : OneHighMissTable) : Bool :=
  oneHighSourcePairingCompatible table 0 [(2, 2)] &&
  oneHighSourcePairingCompatible table 2 [(0, 0)]

theorem oneHighTableHasProfileTwoReciprocalDiagonalCycle_of_mem
    {table : OneHighMissTable}
    (hzero : [(2, 2)] ∈ oneHighCompatibleSourcePairings 2 table 0)
    (htwo : [(0, 0)] ∈ oneHighCompatibleSourcePairings 2 table 2) :
    oneHighTableHasProfileTwoReciprocalDiagonalCycle table = true := by
  rw [oneHighTableHasProfileTwoReciprocalDiagonalCycle, Bool.and_eq_true]
  exact ⟨(List.mem_filter.mp hzero).2, (List.mem_filter.mp htwo).2⟩

theorem oneHighTableHasProfileTwoReciprocalDiagonalCycle_sound
    {table : OneHighMissTable}
    (hcycle : oneHighTableHasProfileTwoReciprocalDiagonalCycle table = true) :
    [(2, 2)] ∈ oneHighCompatibleSourcePairings 2 table 0 ∧
      [(0, 0)] ∈ oneHighCompatibleSourcePairings 2 table 2 := by
  rw [oneHighTableHasProfileTwoReciprocalDiagonalCycle,
    Bool.and_eq_true] at hcycle
  constructor
  · rw [oneHighCompatibleSourcePairings, List.mem_filter]
    exact ⟨by native_decide, hcycle.1⟩
  · rw [oneHighCompatibleSourcePairings, List.mem_filter]
    exact ⟨by native_decide, hcycle.2⟩

def oneHighProfileTwoReciprocalDiagonalCycleInventoryTables :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables 2).filter
    oneHighTableHasProfileTwoReciprocalDiagonalCycle

theorem oneHighProfileTwoReciprocalDiagonalCycleInventoryTables_length :
    oneHighProfileTwoReciprocalDiagonalCycleInventoryTables.length = 78 := by
  native_decide

/-- Adding the reachable all-even requirement leaves only 62 profile-two
rows in the reciprocal-diagonal-cycle arm. -/
def oneHighProfileTwoAllEvenReciprocalDiagonalCycleInventoryTables :
    List OneHighMissTable :=
  oneHighProfileTwoReciprocalDiagonalCycleInventoryTables.filter
    (oneHighTableHasAllEvenPairing 2)

theorem oneHighProfileTwoAllEvenReciprocalDiagonalCycleInventoryTables_length :
    oneHighProfileTwoAllEvenReciprocalDiagonalCycleInventoryTables.length = 62 := by
  native_decide

/-- The exact reciprocal cycle removes 1,545 of the profile-two rows that
only require some source-zero diagonal singleton. -/
theorem oneHighProfileTwoReciprocalDiagonalCycle_removed_count :
    (oneHighReciprocalSingletonRowInventoryTables 2).length -
      oneHighProfileTwoReciprocalDiagonalCycleInventoryTables.length = 1545 := by
  native_decide

end Erdos85
