import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1339
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=526 profileIndexed=true rawInventoryTable=true
    orbit=dde56c15b712e8f4
    compact_lrat_sha256=ffdaffa2fcad4ca719a259d6654179f39a424870ed4af2dcb44c00e6b9cdc852
    raw_lrat_sha256=3f93a9ba625476e25e25748987196d294a796894e2837c2ebf7be4b2974f61e5
    cnf_sha256=a366a5655d94724d139f53137135724f3706a34981cdae9f92ff166d5d0700bd
    binary_lrat_sha256=d0e9a6ac3828a220e95a5719f25e45c83d1f6c15639f4a7cf28fdce9d48d412f
    lz4_frame_sha256=aa3265becb07012429388fdfee7e93314f2a47e18bd3634a04088ea7a99b5a29
    packed_lz4_sha256=dda2fec9b84d51939565c861e492345c1a84f0d70c2b2112825029ebeab545c4
    compact_bytes=801654503 binary_bytes=353344164
    lz4_frame_bytes=213601236 packed_lz4_bytes=244115699
    source_cnf_clauses=613140 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01339Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1339, by native_decide⟩

private def h1V2P0I01339ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/dd/dda2fec9b84d51939565c861e492345c1a84f0d70c2b2112825029ebeab545c4.lrat.lz4p7"

private def h1V2P0I01339RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01339ProofText
    213601236 353344164

private def h1V2P0I01339Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01339Table)
    h1V2P0I01339RawProof).toOption.get!

private theorem h1V2P0I01339Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01339Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01339Table).clauses.toList.all
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
private theorem h1V2P0I01339Check :
    LRAT.check h1V2P0I01339Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01339Table)
        h1V2P0I01339RawProof) := by
  native_decide

theorem h1V2P0I01339Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01339Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01339Nonzero
    h1V2P0I01339RawProof h1V2P0I01339Proof h1V2P0I01339Check

def h1V2P0I01339Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01339Table
  checked := h1V2P0I01339Checked

end Erdos85
