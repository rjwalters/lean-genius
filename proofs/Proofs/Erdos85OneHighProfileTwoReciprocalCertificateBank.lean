import Proofs.Erdos85OneHighProfileTwoReciprocalCertificate01c2be116496a476
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal
import Proofs.Erdos85OneHighV2ResidualCertificateAggregation

/-! # Incremental checked bank for the profile-2 reciprocal campaign -/

namespace Erdos85

/-- Kernel-checked certificates accepted so far, in the order of the
authoritative 78-row reciprocal inventory. -/
def oneHighProfileTwoReciprocalCheckedBank :
    List (OneHighFamilyV2CheckedEntry 2) :=
  [oneHighProfileTwoReciprocalEntry01c2be116496a476]

/-- The still-unchecked suffix of the authoritative reciprocal inventory.
This definition shrinks as new checked entries are appended to the bank. -/
def oneHighProfileTwoReciprocalCertificateResidual : List OneHighMissTable :=
  oneHighProfileTwoReciprocalEntryInventoryTables.drop
    oneHighProfileTwoReciprocalCheckedBank.length

/-- The checked bank and its residual are an exact ordered partition of the
authoritative 78-row inventory. -/
theorem oneHighProfileTwoReciprocalCheckedBank_append_residual :
    oneHighFamilyV2CheckedBankTables oneHighProfileTwoReciprocalCheckedBank ++
      oneHighProfileTwoReciprocalCertificateResidual =
        oneHighProfileTwoReciprocalEntryInventoryTables := by
  rw [← List.cons_head_tail
    (by native_decide : oneHighProfileTwoReciprocalEntryInventoryTables ≠ [])]
  simp only [oneHighFamilyV2CheckedBankTables,
    oneHighProfileTwoReciprocalCheckedBank,
    oneHighProfileTwoReciprocalCertificateResidual, List.map_cons,
    List.map_nil, List.length_cons, List.length_nil, Nat.zero_add,
    List.drop_one, List.singleton_append]
  congr

theorem oneHighProfileTwoReciprocalCertificateResidual_length :
    oneHighProfileTwoReciprocalCertificateResidual.length = 77 := by
  native_decide

/-- Once the residual is discharged, the incremental bank supplies exactly
the universal checked hypothesis consumed by the profile-2 terminal. -/
theorem oneHighProfileTwoReciprocalChecked_of_residual
    (hresidual : ∀ table ∈ oneHighProfileTwoReciprocalCertificateResidual,
      OneHighFamilyV2CheckedUnsat 2 table) :
    ∀ table ∈ oneHighProfileTwoReciprocalEntryInventoryTables,
      OneHighFamilyV2CheckedUnsat 2 table :=
  oneHighFamilyV2Checked_of_bank_append_residual
    oneHighProfileTwoReciprocalCheckedBank
    oneHighProfileTwoReciprocalCheckedBank_append_residual
    hresidual

end Erdos85
