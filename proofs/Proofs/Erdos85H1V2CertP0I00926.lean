import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=926
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=368 profileIndexed=true rawInventoryTable=true
    orbit=9c14ed1b8f4a6508
    compact_lrat_sha256=eb4579013b300e149c786efb65aaa9591c04821687453d42b681d1b4cc48a55d
    raw_lrat_sha256=c1901f32d378b6a02a7d627da572bf01e0e95b47b4faacda86f2ff19618c578f
    cnf_sha256=bfe86ef7e06214f5bba0654d88576021156f5d40ad4f5ecfa6862dd0f1521ac1
    binary_lrat_sha256=ce4d5bdf7a2d3ee899868e62f9534ab9269e31ce50b90ac752e2f5050b874e8c
    lz4_frame_sha256=cecfff9bb3c2668848a27878abf8ac92a68ef41d2b60fe29d73c6e52f721d621
    packed_lz4_sha256=78a9a68d17e9a3f7694c95ff7116da6b8e0b38f11d44cbff701d85bf0ba677f2
    compact_bytes=935327450 binary_bytes=412288537
    lz4_frame_bytes=245721267 packed_lz4_bytes=280824306
    source_cnf_clauses=613060 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00926Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨926, by native_decide⟩

private def h1V2P0I00926ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/78/78a9a68d17e9a3f7694c95ff7116da6b8e0b38f11d44cbff701d85bf0ba677f2.lrat.lz4p7"

private def h1V2P0I00926RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00926ProofText
    245721267 412288537

private def h1V2P0I00926Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00926Table)
    h1V2P0I00926RawProof).toOption.get!

private theorem h1V2P0I00926Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00926Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00926Table).clauses.toList.all
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
private theorem h1V2P0I00926Check :
    LRAT.check h1V2P0I00926Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00926Table)
        h1V2P0I00926RawProof) := by
  native_decide

theorem h1V2P0I00926Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00926Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00926Nonzero
    h1V2P0I00926RawProof h1V2P0I00926Proof h1V2P0I00926Check

def h1V2P0I00926Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00926Table
  checked := h1V2P0I00926Checked

end Erdos85
