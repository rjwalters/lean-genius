import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=512
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=6
    orbit=1c31ce69850bce37
    compact_lrat_sha256=375fbfc544d23a4d33b00081d390bea277dd89797d2e3866616ce69bf0c68fc8
    raw_lrat_sha256=8954c4b2a6e4380a95111816ce7fc8558349724dbbadc2e5a31ae06801d8706f
    cnf_sha256=1b4e6f063cc9f20d616ebcbb4c1091f157cecc263a948e2ad64f4f3e05a2b383
    binary_lrat_sha256=eb54aac87f18e80e4c1ce4e2ef125aef0bf27464f12c3ff8bc078fea02800f37
    lz4_frame_sha256=660790ff7062d6757d7430f43dfd10a6dcbabc708ab207f515437d078b7435af
    packed_lz4_sha256=a4dafa805553f9500773d5faf51e2b8157c83cd8224c4ea83bb34ed0e3919872
    compact_bytes=315678135 binary_bytes=139012259
    lz4_frame_bytes=85120403 packed_lz4_bytes=97280461
    source_cnf_clauses=610276 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00512Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨6, by native_decide⟩

private def h1V2P2I00512ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/a4/a4dafa805553f9500773d5faf51e2b8157c83cd8224c4ea83bb34ed0e3919872.lrat.lz4p7"

private def h1V2P2I00512RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00512ProofText
    85120403 139012259

private def h1V2P2I00512Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00512Table)
    h1V2P2I00512RawProof).toOption.get!

private theorem h1V2P2I00512Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00512Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00512Table).clauses.toList.all
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
private theorem h1V2P2I00512Check :
    LRAT.check h1V2P2I00512Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00512Table)
        h1V2P2I00512RawProof) := by
  native_decide

theorem h1V2P2I00512Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00512Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00512Nonzero
    h1V2P2I00512RawProof h1V2P2I00512Proof h1V2P2I00512Check

def h1V2P2I00512Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00512Table
  checked := h1V2P2I00512Checked

end Erdos85
