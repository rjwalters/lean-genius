import Proofs.Erdos85OneHighProfileTwoReciprocalCertificate01c2be116496a476
import Proofs.Erdos85H1V2CertP2I00101
import Proofs.Erdos85H1V2CertP2I00132
import Proofs.Erdos85H1V2CertP2I00166
import Proofs.Erdos85H1V2CertP2I00341
import Proofs.Erdos85H1V2CertP2I00499
import Proofs.Erdos85H1V2CertP2I00512
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal
import Proofs.Erdos85OneHighV2ResidualCertificateAggregation

/-! # Incremental checked bank for the profile-2 reciprocal campaign -/

namespace Erdos85

/-- Kernel-checked certificates accepted so far, in the order of the
authoritative 78-row reciprocal inventory. -/
def oneHighProfileTwoReciprocalCheckedBank :
    List (OneHighFamilyV2CheckedEntry 2) :=
  [ oneHighProfileTwoReciprocalEntry01c2be116496a476,
    h1V2P2I00101Entry,
    h1V2P2I00132Entry,
    h1V2P2I00166Entry,
    h1V2P2I00341Entry,
    h1V2P2I00499Entry,
    h1V2P2I00512Entry ]

/-- The still-unchecked suffix of the authoritative reciprocal inventory.
This definition shrinks as new checked entries are appended to the bank. -/
def oneHighProfileTwoReciprocalCertificateResidual : List OneHighMissTable :=
  oneHighProfileTwoReciprocalEntryInventoryTables.drop
    oneHighProfileTwoReciprocalCheckedBank.length

/-- Proof erasure of the checked entries gives exactly the first seven rows
of the authoritative reciprocal inventory. -/
theorem oneHighProfileTwoReciprocalCheckedBank_tables_eq_take :
    oneHighFamilyV2CheckedBankTables oneHighProfileTwoReciprocalCheckedBank =
      oneHighProfileTwoReciprocalEntryInventoryTables.take
        oneHighProfileTwoReciprocalCheckedBank.length := by
  apply List.ext_get
  · simp [oneHighFamilyV2CheckedBankTables,
      oneHighProfileTwoReciprocalCheckedBank,
      oneHighProfileTwoReciprocalEntryInventoryTables_length]
  · intro n hbank htake
    have hn : n < 7 := by
      simpa [oneHighFamilyV2CheckedBankTables,
        oneHighProfileTwoReciprocalCheckedBank] using hbank
    interval_cases n
    · simpa [oneHighFamilyV2CheckedBankTables,
        oneHighProfileTwoReciprocalCheckedBank,
        oneHighProfileTwoReciprocalEntry01c2be116496a476,
        oneHighProfileTwoReciprocalTable01c2be116496a476] using
        (List.head_eq_getElem
          (by native_decide :
            oneHighProfileTwoReciprocalEntryInventoryTables ≠ []))
    all_goals
      simp [oneHighFamilyV2CheckedBankTables,
        oneHighProfileTwoReciprocalCheckedBank,
        h1V2P2I00101Entry, h1V2P2I00101Table,
        h1V2P2I00132Entry, h1V2P2I00132Table,
        h1V2P2I00166Entry, h1V2P2I00166Table,
        h1V2P2I00341Entry, h1V2P2I00341Table,
        h1V2P2I00499Entry, h1V2P2I00499Table,
        h1V2P2I00512Entry, h1V2P2I00512Table]

/-- The checked seven-row prefix and its residual are an exact ordered
partition of the authoritative 78-row inventory. -/
theorem oneHighProfileTwoReciprocalCheckedBank_append_residual :
    oneHighFamilyV2CheckedBankTables oneHighProfileTwoReciprocalCheckedBank ++
      oneHighProfileTwoReciprocalCertificateResidual =
        oneHighProfileTwoReciprocalEntryInventoryTables := by
  rw [oneHighProfileTwoReciprocalCheckedBank_tables_eq_take]
  exact List.take_append_drop _ _

theorem oneHighProfileTwoReciprocalCertificateResidual_length :
    oneHighProfileTwoReciprocalCertificateResidual.length = 71 := by
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
