import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=326
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=137 profileIndexed=true rawInventoryTable=true
    orbit=35c284aad6ba17cf
    compact_lrat_sha256=ce484b64dbcbc005767b0e471ac42127c56e25b8acccf510caa56ce574ceb431
    raw_lrat_sha256=274542e3d1ca5e616ddd1397e2503435b34bedf2f2561b170fabec91f3c89f6c
    cnf_sha256=fb1e9f9c374dc99523a849243d5085a3c87e20baa4f22524b2653dca6e1bd659
    binary_lrat_sha256=24f195d98822900600de1882345134026e92d677f563466cab0e640abdae48db
    lz4_frame_sha256=dc73d9a7fb9ce9e295fa14107917d6948c11cd2f7312216c55ec41c4e7971d21
    packed_lz4_sha256=8973ea690112616ecd8a1906cbeb954f0639885b7f0b8820eeb2a860c6e39207
    compact_bytes=150835912 binary_bytes=65747400
    lz4_frame_bytes=35773411 packed_lz4_bytes=40883899
    source_cnf_clauses=613072 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00326Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨326, by native_decide⟩

private def h1V2P0I00326ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/89/8973ea690112616ecd8a1906cbeb954f0639885b7f0b8820eeb2a860c6e39207.lrat.lz4p7"

private def h1V2P0I00326RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00326ProofText
    35773411 65747400

private def h1V2P0I00326Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00326Table)
    h1V2P0I00326RawProof).toOption.get!

private theorem h1V2P0I00326Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00326Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00326Table).clauses.toList.all
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
private theorem h1V2P0I00326Check :
    LRAT.check h1V2P0I00326Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00326Table)
        h1V2P0I00326RawProof) := by
  native_decide

theorem h1V2P0I00326Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00326Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00326Nonzero
    h1V2P0I00326RawProof h1V2P0I00326Proof h1V2P0I00326Check

def h1V2P0I00326Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00326Table
  checked := h1V2P0I00326Checked

end Erdos85
