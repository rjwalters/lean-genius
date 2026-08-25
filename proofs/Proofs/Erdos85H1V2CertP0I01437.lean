import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1437
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=563 profileIndexed=true rawInventoryTable=true
    orbit=f04fd8e14a7d9e62
    compact_lrat_sha256=2fbdbfe0c7f1fc68f8ccd2019484f095ab9716029656de5e8ecb2f3cab7180bd
    raw_lrat_sha256=ff33f79793c89142d8e878fc4dc7b3c74264d5699073e06f06ba21b25847bcc8
    cnf_sha256=2dff3770f0a489f1d95897676e73257e703e654bdef8f5fb1422d08fe577775e
    binary_lrat_sha256=365bc18c42ed3bfb9ec03dba630db0a5eff919c9e8520331b91d0527a0d3f21f
    lz4_frame_sha256=40cc5625c815721a5da3b38acf16f5aa63c3ca05ada01f4f0272ac430878a106
    packed_lz4_sha256=b4774bcbf5335018b53c8c4ca8f329e37ffde42fe320afed16a28d0212a5159a
    compact_bytes=1747525871 binary_bytes=776186487
    lz4_frame_bytes=440913802 packed_lz4_bytes=503901488
    source_cnf_clauses=613228 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01437Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1437, by native_decide⟩

private def h1V2P0I01437ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b4/b4774bcbf5335018b53c8c4ca8f329e37ffde42fe320afed16a28d0212a5159a.lrat.lz4p7"

private def h1V2P0I01437RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01437ProofText
    440913802 776186487

private def h1V2P0I01437Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01437Table)
    h1V2P0I01437RawProof).toOption.get!

private theorem h1V2P0I01437Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01437Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01437Table).clauses.toList.all
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
private theorem h1V2P0I01437Check :
    LRAT.check h1V2P0I01437Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01437Table)
        h1V2P0I01437RawProof) := by
  native_decide

theorem h1V2P0I01437Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01437Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01437Nonzero
    h1V2P0I01437RawProof h1V2P0I01437Proof h1V2P0I01437Check

def h1V2P0I01437Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01437Table
  checked := h1V2P0I01437Checked

end Erdos85
