import Proofs.Erdos85OneHighV2RelabeledPresentation

/-! # Kernel-readable authoritative h=1 orbit inventory -/

namespace Erdos85

/-- One compact artifact row: profile plus the 24 upper non-mate values in
`oneHighFamilyTablePairs` order. -/
structure OneHighInventoryRow where
  profile : Fin 5
  values : List Nat
  values_length : values.length = 24

def oneHighInventoryRowTable (row : OneHighInventoryRow) :
    OneHighMissTable := fun c j =>
  match (oneHighFamilyTablePairs.zip row.values).find?
      (fun entry => entry.1 = (c, j)) with
  | some entry => entry.2
  | none => 0

def oneHighInventoryRowFiniteTable (row : OneHighInventoryRow) :
    OneHighFiniteMissTable := fun pair =>
  ⟨oneHighInventoryRowTable row pair.1.1.val pair.1.2.val % 5,
    Nat.mod_lt _ (by omega)⟩

def parseOneHighInventoryRow (line : String) : Option OneHighInventoryRow := do
  let fields ← (line.splitOn " ").mapM String.toNat?
  let profileNat ← fields.head?
  let values := fields.tail
  if hp : profileNat < 5 then
    if hv : values.length = 24 then
      some ⟨⟨profileNat, hp⟩, values, hv⟩
    else none
  else none

def oneHighInventoryText : String :=
  include_str "Certificates" / "h1_orbit_inventory.compact"

def oneHighInventoryRows : List OneHighInventoryRow :=
  (oneHighInventoryText.splitOn "\n").filterMap parseOneHighInventoryRow

def oneHighInventoryTables (profile : Fin 5) : List OneHighMissTable :=
  oneHighInventoryRows.filterMap fun row =>
    if row.profile = profile then some (oneHighInventoryRowTable row) else none

def oneHighInventoryFiniteTables
    (profile : Fin 5) : List OneHighFiniteMissTable :=
  oneHighInventoryRows.filterMap fun row =>
    if row.profile = profile then
      some (oneHighInventoryRowFiniteTable row)
    else none

/-- The compact artifact parses without losing or adding a row. -/
theorem oneHighInventoryRows_length : oneHighInventoryRows.length = 13541 := by
  native_decide

theorem oneHighInventoryRows_values_lt_five :
    ∀ row ∈ oneHighInventoryRows, ∀ value ∈ row.values, value < 5 := by
  native_decide

theorem oneHighInventoryRows_keys_nodup :
    (oneHighInventoryRows.map fun row =>
      (row.profile.val, row.values)).Nodup := by
  native_decide

/-- Independently checked per-profile census, in generator profile order
BBBB, ABBB, AABB, AAAB, AAAA. -/
theorem oneHighInventoryTables_length_zero :
    (oneHighInventoryTables 0).length = 1536 := by native_decide

theorem oneHighInventoryTables_length_one :
    (oneHighInventoryTables 1).length = 3662 := by native_decide

theorem oneHighInventoryTables_length_two :
    (oneHighInventoryTables 2).length = 4801 := by native_decide

theorem oneHighInventoryTables_length_three :
    (oneHighInventoryTables 3).length = 2700 := by native_decide

theorem oneHighInventoryTables_length_four :
    (oneHighInventoryTables 4).length = 842 := by native_decide

end Erdos85
