import Proofs.Erdos85OneHighTurnRowInventory
import Proofs.Erdos85OneHighKnownSectorParity

/-! # Compact parity-state inventory for the saturated odd turn -/

namespace Erdos85

/-- Reachable parity masks after fixing one source branch to one particular
compatible pairing row.  Deduplication at every remaining source avoids the
full Cartesian refinement enumeration. -/
def oneHighPairingParityStatesWithSourceRow
    (profile : Nat) (table : OneHighMissTable)
    (source : Fin 8) (row : List OneHighLabelPair) : List Nat :=
  oneHighChooseEachParityStates
    (List.ofFn fun current : Fin 8 =>
      if current = source then [row]
      else oneHighCompatibleSourcePairings profile table current)

/-- Reachable parity masks contributed by all branches except one fixed
source.  The omitted source contributes the unique empty row (mask zero). -/
def oneHighPairingParityStatesWithoutSource
    (profile : Nat) (table : OneHighMissTable)
    (source : Fin 8) : List Nat :=
  oneHighChooseEachParityStates
    (List.ofFn fun current : Fin 8 =>
      if current = source then [[]]
      else oneHighCompatibleSourcePairings profile table current)

/-- Precomputed-choice variant used by the inventory scan, so the eight
compatible source-row lists are generated only once per table. -/
def oneHighPairingParityStatesWithoutSourceChoices
    (choices : List (List (List OneHighLabelPair)))
    (source : Fin 8) : List Nat :=
  oneHighChooseEachParityStates (choices.set source.val [[]])

/-- Precomputed-choice fixed-row state image. -/
def oneHighPairingParityStatesWithSourceRowChoices
    (choices : List (List (List OneHighLabelPair)))
    (source : Fin 8) (row : List OneHighLabelPair) : List Nat :=
  oneHighChooseEachParityStates (choices.set source.val [row])

/-- Turn labelings realized by one fixed owner row, computed before any
global parity states.  Most compatible rows have no such labeling, so this
local prefilter avoids running the state fold for them. -/
def oneHighSaturatedTurnRowTriples
    (source : Fin 8) (row : List OneHighLabelPair) :
    List (Fin 8 × Fin 8 × Fin 8) :=
  let labels := (row.flatMap fun pair => [pair.1, pair.2]).eraseDups
  labels.flatMap fun a =>
    labels.flatMap fun b =>
      labels.filterMap fun c =>
        if row.Perm [oneHighCanonicalLabelPair a b,
            oneHighCanonicalLabelPair b c] ∧
          oneHighRootPair source ≠ oneHighRootPair a ∧
          oneHighRootPair source ≠ oneHighRootPair b ∧
          oneHighRootPair source ≠ oneHighRootPair c ∧
          oneHighRootPair a ≠ oneHighRootPair b ∧
          oneHighRootPair b ≠ oneHighRootPair c ∧
          oneHighRootPair a ≠ oneHighRootPair c then
          some (a, b, c)
        else none

/-- Compact implementation of the exact saturated odd-turn existential.
It fixes the saturated owner row first and explores only deduplicated parity
states for the other seven source branches. -/
def oneHighTableHasSaturatedOddThreePairTurnByParity
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  let choices := List.ofFn fun source : Fin 8 =>
    oneHighCompatibleSourcePairings profile table source
  (List.ofFn fun source : Fin 8 => source).any fun source =>
    let rows := choices[source.val]!.filter fun row =>
      !(oneHighSaturatedTurnRowTriples source row).isEmpty
    !rows.isEmpty &&
      rows.any fun row =>
        let triples := oneHighSaturatedTurnRowTriples source row
        (oneHighPairingParityStatesWithSourceRowChoices
          choices source row).any fun mask =>
          triples.any fun triple =>
            oneHighParityMaskOdd mask triple.1 triple.2.1 &&
              oneHighParityMaskOdd mask triple.2.1 triple.2.2

def oneHighSaturatedOddTurnParityInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasSaturatedOddThreePairTurnByParity profile.val)

/-- The compact exact implementation reproduces the 9,707-row diagnostic,
with an authoritative per-profile breakdown. -/
theorem oneHighSaturatedOddTurnParityInventory_profile_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighSaturatedOddTurnParityInventoryTables profile).length) =
      [1136, 2923, 3328, 1873, 447] := by
  native_decide

theorem oneHighSaturatedOddTurnParityInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighSaturatedOddTurnParityInventoryTables profile).length).sum =
      9707 := by
  rw [oneHighSaturatedOddTurnParityInventory_profile_lengths]
  norm_num

end Erdos85
