import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1487
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=589 profileIndexed=true rawInventoryTable=true
    orbit=f7e1d45069e7ade7
    compact_lrat_sha256=6c9b91c10c424d3c0e3028880dd6d8ef96dc4271f21734e95488585e97b35f9b
    raw_lrat_sha256=6c7872b5eb778b4516be667cadbcf8a2880e850293f55198defde598c437b2e9
    cnf_sha256=979a41da9a3222164f7102ce6e6b83fc916f8ee8a56c5f4c239630b600039e21
    binary_lrat_sha256=6c277390ec9f78b722f20aebd87de5d4fc820c035401cc9cbfa66996448e79f8
    lz4_frame_sha256=e21cb5d91ff50bb843bf4d680e1c8c2691f47526b2ff65ef2af58ae45711b85d
    packed_lz4_sha256=6a591bdad156f2f235a996ba96786ab40d78fb28d67c666f394ec214d2e22f37
    compact_bytes=1716587505 binary_bytes=758097457
    lz4_frame_bytes=447055240 packed_lz4_bytes=510920275
    source_cnf_clauses=613052 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01487Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1487, by native_decide⟩

private def h1V2P0I01487ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/6a/6a591bdad156f2f235a996ba96786ab40d78fb28d67c666f394ec214d2e22f37.lrat.lz4p7"

private def h1V2P0I01487RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01487ProofText
    447055240 758097457

private def h1V2P0I01487Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01487Table)
    h1V2P0I01487RawProof).toOption.get!

private theorem h1V2P0I01487Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01487Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01487Table).clauses.toList.all
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
private theorem h1V2P0I01487Check :
    LRAT.check h1V2P0I01487Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01487Table)
        h1V2P0I01487RawProof) := by
  native_decide

theorem h1V2P0I01487Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01487Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01487Nonzero
    h1V2P0I01487RawProof h1V2P0I01487Proof h1V2P0I01487Check

def h1V2P0I01487Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01487Table
  checked := h1V2P0I01487Checked

end Erdos85
