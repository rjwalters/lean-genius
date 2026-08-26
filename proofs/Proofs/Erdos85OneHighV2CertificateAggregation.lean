import Proofs.Erdos85OneHighV2InventoryCover

/-!
# Scalable aggregation of exact-v2 one-high certificates

Each solver certificate can live in a small independent module and export a
`OneHighFamilyV2CheckedUnsat` theorem.  This file packages those theorems as
entries in an ordered bank.  A bank whose projected table list is exactly the
authoritative inventory supplies the universal hypothesis required by
`orderFortyNineStratumExcluded_one_of_inventory_checked`.

The coverage equality deliberately mentions no LRAT representation.  It can
therefore be proved by `rfl` when generated stubs are emitted in inventory
order, or checked separately from compact table data without rebuilding the
individual certificates.
-/

namespace Erdos85

/-- One checked representative, retaining the table in its index so that no
hash or tag is part of the trusted interface. -/
structure OneHighFamilyV2CheckedEntry (profile : Nat) where
  table : OneHighMissTable
  checked : OneHighFamilyV2CheckedUnsat profile table

/-- Forget the proofs in a certificate bank and retain its ordered tables. -/
def oneHighFamilyV2CheckedBankTables {profile : Nat}
    (bank : List (OneHighFamilyV2CheckedEntry profile)) :
    List OneHighMissTable :=
  bank.map OneHighFamilyV2CheckedEntry.table

/-- Membership in a checked bank yields checked-UNSAT evidence for the
corresponding table. -/
theorem oneHighFamilyV2Checked_of_mem_bank
    {profile : Nat} (bank : List (OneHighFamilyV2CheckedEntry profile))
    {table : OneHighMissTable}
    (hmem : table ∈ oneHighFamilyV2CheckedBankTables bank) :
    OneHighFamilyV2CheckedUnsat profile table := by
  rw [oneHighFamilyV2CheckedBankTables] at hmem
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
  exact entry.checked

/-- An ordered bank covering one authoritative profile supplies every
certificate required for that profile. -/
theorem oneHighFamilyV2Checked_of_bank_tables_eq_inventory
    (profile : Fin 5)
    (bank : List (OneHighFamilyV2CheckedEntry profile.val))
    (hcover : oneHighFamilyV2CheckedBankTables bank =
      oneHighInventoryTables profile) :
    ∀ table ∈ oneHighInventoryTables profile,
      OneHighFamilyV2CheckedUnsat profile.val table := by
  intro table htable
  apply oneHighFamilyV2Checked_of_mem_bank bank
  rw [hcover]
  exact htable

/-- Indexed checked evidence for every position in an inventory list supplies
the same universal interface without requiring decidable equality on miss
tables.  This is the scalable socket for generated certificate dispatchers. -/
theorem oneHighFamilyV2Checked_of_inventory_get
    (profile : Fin 5)
    (hchecked : ∀ i : Fin (oneHighInventoryTables profile).length,
      OneHighFamilyV2CheckedUnsat profile.val
        ((oneHighInventoryTables profile).get i)) :
    ∀ table ∈ oneHighInventoryTables profile,
      OneHighFamilyV2CheckedUnsat profile.val table := by
  intro table htable
  obtain ⟨i, hi⟩ := List.get_of_mem htable
  rw [← hi]
  exact hchecked i

/-- Five ordered certificate banks close the exact-v2 one-high stratum.

This is the aggregation socket for generated per-orbit LRAT modules.  The
only coverage obligation is equality of the proof-erased table projections
with the five authoritative inventory lists. -/
theorem orderFortyNineStratumExcluded_one_of_checked_banks
    (bank : ∀ profile : Fin 5,
      List (OneHighFamilyV2CheckedEntry profile.val))
    (hcover : ∀ profile : Fin 5,
      oneHighFamilyV2CheckedBankTables (bank profile) =
        oneHighInventoryTables profile) :
    OrderFortyNineStratumExcluded 1 := by
  apply orderFortyNineStratumExcluded_one_of_inventory_checked
  intro profile table htable
  exact oneHighFamilyV2Checked_of_bank_tables_eq_inventory
    profile (bank profile) (hcover profile) table htable

end Erdos85
