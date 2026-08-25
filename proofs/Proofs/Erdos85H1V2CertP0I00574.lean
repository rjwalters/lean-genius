import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=574
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=221 profileIndexed=true rawInventoryTable=true
    orbit=61cfc22964303b04
    compact_lrat_sha256=0a9b8f55524e9d3ca28e9dfb8e4b9595e42baad1e16eff7da39ff97baf309557
    raw_lrat_sha256=3942df8ef43eab685b16af56ae38f5a5cbe4b94fd9beb0ab2c21bdcf44b8bfe2
    cnf_sha256=78c4d11a551d31475bdc2b98f72446dfe82a6d0c755efaf6cfa596c02a20f26d
    binary_lrat_sha256=b4da0948bb4f3dadee416bcc96a60bf13653d4b1c9012bcf0e0fccb74f096e79
    lz4_frame_sha256=572953c2201e1a6d7366f447ecf769bd20e5400c4fade6ea622d18cb36ad024f
    packed_lz4_sha256=2ac41a96cf27ad1d14b57c071d6418d86d6d78ecc80eb6f429ec7bf426afca13
    compact_bytes=784466459 binary_bytes=347433663
    lz4_frame_bytes=212783622 packed_lz4_bytes=243181283
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00574Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨574, by native_decide⟩

private def h1V2P0I00574ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/2a/2ac41a96cf27ad1d14b57c071d6418d86d6d78ecc80eb6f429ec7bf426afca13.lrat.lz4p7"

private def h1V2P0I00574RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00574ProofText
    212783622 347433663

private def h1V2P0I00574Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00574Table)
    h1V2P0I00574RawProof).toOption.get!

private theorem h1V2P0I00574Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00574Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00574Table).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause
      (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem h1V2P0I00574Check :
    LRAT.check h1V2P0I00574Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00574Table)
        h1V2P0I00574RawProof) := by
  native_decide

theorem h1V2P0I00574Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00574Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00574Nonzero
    h1V2P0I00574RawProof h1V2P0I00574Proof h1V2P0I00574Check

def h1V2P0I00574Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00574Table
  checked := h1V2P0I00574Checked

end Erdos85
