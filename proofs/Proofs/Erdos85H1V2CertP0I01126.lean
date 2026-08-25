import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1126
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=447 profileIndexed=true rawInventoryTable=true
    orbit=bc73358c583890cd
    compact_lrat_sha256=cab046cd5599cc34879d1ec2c03c7df832531010b52b3e5d98b931436766b716
    raw_lrat_sha256=c27e93b78fd763f2bfab8c9587b74c841b663760f041ae5340e713e3855185e2
    cnf_sha256=100a2d909dc0ee4a1bd3ce87d1490993c9e91f81f64368a189f909520fb97489
    binary_lrat_sha256=f668acd3bbfdc82a00f833414629c5928cf6a721b72505ee2171024f25f8a9bb
    lz4_frame_sha256=7ae0fb280de63426113c3be42325c702acb7f322464ab42f65abff1c5ec150af
    packed_lz4_sha256=fd6012b3ea828922bd0a71ecef49223f79318243da1d61a8d406d41914933dfc
    compact_bytes=1485780304 binary_bytes=657369625
    lz4_frame_bytes=389043457 packed_lz4_bytes=444621094
    source_cnf_clauses=613140 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01126Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1126, by native_decide⟩

private def h1V2P0I01126ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/fd/fd6012b3ea828922bd0a71ecef49223f79318243da1d61a8d406d41914933dfc.lrat.lz4p7"

private def h1V2P0I01126RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01126ProofText
    389043457 657369625

private def h1V2P0I01126Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01126Table)
    h1V2P0I01126RawProof).toOption.get!

private theorem h1V2P0I01126Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01126Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01126Table).clauses.toList.all
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
private theorem h1V2P0I01126Check :
    LRAT.check h1V2P0I01126Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01126Table)
        h1V2P0I01126RawProof) := by
  native_decide

theorem h1V2P0I01126Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01126Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01126Nonzero
    h1V2P0I01126RawProof h1V2P0I01126Proof h1V2P0I01126Check

def h1V2P0I01126Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01126Table
  checked := h1V2P0I01126Checked

end Erdos85
