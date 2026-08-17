import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=560
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=9
    orbit=1ed9e3aec4747e88
    compact_lrat_sha256=281412240b3aa227ef540d7198d956182f2fee0a526f56c4e07090a6bd9136d4
    raw_lrat_sha256=bdda417010d272ac9699b6bd3be2f630edddb6ccccde8a28b613cdce7165161f
    cnf_sha256=351bb8632a8e5e7d7a28bc25c019a6d6892e926a226fbd8b019fea22d71deaf3
    binary_lrat_sha256=6022f4a939b9e06674b1aa78b547b49e96d0f2e973e17034d1756c4a90b3934a
    lz4_frame_sha256=7d0fc5d5521933481d927213e06dc564d68d41f8865133313f6e2db164d4b533
    packed_lz4_sha256=6f148c3105efd98917d85c496c1c57ef998ca1d6a12335aceac4b67080d4d51d
    compact_bytes=233786322 binary_bytes=102015299
    lz4_frame_bytes=63891607 packed_lz4_bytes=73018980
    source_cnf_clauses=610278 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00560Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨9, by native_decide⟩

private def h1V2P2I00560ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/6f/6f148c3105efd98917d85c496c1c57ef998ca1d6a12335aceac4b67080d4d51d.lrat.lz4p7"

private def h1V2P2I00560RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00560ProofText
    63891607 102015299

private def h1V2P2I00560Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00560Table)
    h1V2P2I00560RawProof).toOption.get!

private theorem h1V2P2I00560Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00560Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00560Table).clauses.toList.all
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
private theorem h1V2P2I00560Check :
    LRAT.check h1V2P2I00560Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00560Table)
        h1V2P2I00560RawProof) := by
  native_decide

theorem h1V2P2I00560Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00560Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00560Nonzero
    h1V2P2I00560RawProof h1V2P2I00560Proof h1V2P2I00560Check

def h1V2P2I00560Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00560Table
  checked := h1V2P2I00560Checked

end Erdos85
