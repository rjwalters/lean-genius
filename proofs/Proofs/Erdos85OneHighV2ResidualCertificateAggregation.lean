import Proofs.Erdos85OneHighV2CertificateAggregation

/-! # Incremental aggregation of exact-v2 certificate campaigns -/

namespace Erdos85

/-- A checked prefix bank plus checked evidence for the remaining ordered
suffix supplies checked evidence for the whole inventory.  This lets a long
certificate campaign shrink its trusted residual after every accepted proof,
without regenerating one monolithic theorem. -/
theorem oneHighFamilyV2Checked_of_bank_append_residual
    {profile : Nat} {inventory residual : List OneHighMissTable}
    (bank : List (OneHighFamilyV2CheckedEntry profile))
    (hcover : oneHighFamilyV2CheckedBankTables bank ++ residual = inventory)
    (hresidual : ∀ table ∈ residual,
      OneHighFamilyV2CheckedUnsat profile table) :
    ∀ table ∈ inventory, OneHighFamilyV2CheckedUnsat profile table := by
  intro table htable
  rw [← hcover, List.mem_append] at htable
  rcases htable with hbank | hresidualMem
  · exact oneHighFamilyV2Checked_of_mem_bank bank hbank
  · exact hresidual table hresidualMem

/-- Empty residual: an incrementally assembled bank whose table projection is
the target inventory closes that inventory directly. -/
theorem oneHighFamilyV2Checked_of_bank_append_nil
    {profile : Nat} {inventory : List OneHighMissTable}
    (bank : List (OneHighFamilyV2CheckedEntry profile))
    (hcover : oneHighFamilyV2CheckedBankTables bank ++ [] = inventory) :
    ∀ table ∈ inventory, OneHighFamilyV2CheckedUnsat profile table := by
  apply oneHighFamilyV2Checked_of_bank_append_residual bank hcover
  intro table hmem
  simp at hmem

/-- One newly checked head can be prepended to an existing residual bank
without changing the projected table order. -/
def OneHighFamilyV2CheckedEntry.consBank
    {profile : Nat} (entry : OneHighFamilyV2CheckedEntry profile)
    (bank : List (OneHighFamilyV2CheckedEntry profile)) :
    List (OneHighFamilyV2CheckedEntry profile) :=
  entry :: bank

@[simp] theorem oneHighFamilyV2CheckedBankTables_consBank
    {profile : Nat} (entry : OneHighFamilyV2CheckedEntry profile)
    (bank : List (OneHighFamilyV2CheckedEntry profile)) :
    oneHighFamilyV2CheckedBankTables (entry.consBank bank) =
      entry.table :: oneHighFamilyV2CheckedBankTables bank := by
  rfl

end Erdos85
