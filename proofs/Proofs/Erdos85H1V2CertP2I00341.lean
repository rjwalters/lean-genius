import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=341
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=4
    orbit=1183454452377291
    compact_lrat_sha256=36c867194107f68dd5b981b2567a4139ff03dc3ce121b6a28fecd3ca4ae86f0b
    raw_lrat_sha256=c69c207497d248e59cfd93e1addd0a8e61b1233a2ced35b6a53395a96b92d19d
    cnf_sha256=87127bdba890663803fbb08e3dfe9319907086a67f3838c20633dcbbdb397ab9
    binary_lrat_sha256=6c72a401abf267fdb9aa38616b6b3d52cf7bbe86e3c7d33048b71182e00d6091
    lz4_frame_sha256=d78cb8ea74b540073b994c61a3270348010801ebbc36f843d1fbd9779de22132
    packed_lz4_sha256=d99fba4beba7852c53170e71484e4be772f773b8b6c731fed75f039b9390a569
    compact_bytes=465105765 binary_bytes=207139000
    lz4_frame_bytes=127112907 packed_lz4_bytes=145271894
    source_cnf_clauses=610252 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00341Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨4, by native_decide⟩

private def h1V2P2I00341ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/d9/d99fba4beba7852c53170e71484e4be772f773b8b6c731fed75f039b9390a569.lrat.lz4p7"

private def h1V2P2I00341RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00341ProofText
    127112907 207139000

private def h1V2P2I00341Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00341Table)
    h1V2P2I00341RawProof).toOption.get!

private theorem h1V2P2I00341Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00341Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00341Table).clauses.toList.all
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
private theorem h1V2P2I00341Check :
    LRAT.check h1V2P2I00341Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00341Table)
        h1V2P2I00341RawProof) := by
  native_decide

theorem h1V2P2I00341Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00341Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00341Nonzero
    h1V2P2I00341RawProof h1V2P2I00341Proof h1V2P2I00341Check

def h1V2P2I00341Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00341Table
  checked := h1V2P2I00341Checked

end Erdos85
