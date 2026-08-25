import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=66
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=29 profileIndexed=true rawInventoryTable=true
    orbit=09c7600162e4a5f3
    compact_lrat_sha256=87f9e50770b5c58ed445aed5ef7a82f836b29f60df958179b7b4f23b551d4212
    raw_lrat_sha256=fb269715e1097a09b01db1e86a670189dc7f8ed31b702cb289c8f1851cf98456
    cnf_sha256=ef5836f6f7ad1d49c8f17718ae8090cd6288a2fe6ac09d796d7a4ea61a260420
    binary_lrat_sha256=f2eb4a3d8b16a339aa7fc113553360b158d291179c9d84fc90f38bd3360893c0
    lz4_frame_sha256=3f987343fc65832b012ea4ce8a992793afc039e90d2f80e02f5676662f87c626
    packed_lz4_sha256=34ca22d4ba43e72ab47d62122b3084f7b6a05d5018aa797a33007b9b4fa1b238
    compact_bytes=615359208 binary_bytes=270675234
    lz4_frame_bytes=155945408 packed_lz4_bytes=178223324
    source_cnf_clauses=613146 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00066Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨66, by native_decide⟩

private def h1V2P0I00066ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/34/34ca22d4ba43e72ab47d62122b3084f7b6a05d5018aa797a33007b9b4fa1b238.lrat.lz4p7"

private def h1V2P0I00066RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00066ProofText
    155945408 270675234

private def h1V2P0I00066Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00066Table)
    h1V2P0I00066RawProof).toOption.get!

private theorem h1V2P0I00066Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00066Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00066Table).clauses.toList.all
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
private theorem h1V2P0I00066Check :
    LRAT.check h1V2P0I00066Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00066Table)
        h1V2P0I00066RawProof) := by
  native_decide

theorem h1V2P0I00066Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00066Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00066Nonzero
    h1V2P0I00066RawProof h1V2P0I00066Proof h1V2P0I00066Check

def h1V2P0I00066Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00066Table
  checked := h1V2P0I00066Checked

end Erdos85
