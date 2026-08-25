import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=85
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=39 profileIndexed=true rawInventoryTable=true
    orbit=0c4be381b3bbd7aa
    compact_lrat_sha256=2620c11797a7608489937e1c1052188c5d00e4d9faba6b930199542c33e53f6f
    raw_lrat_sha256=61d4f97195278ceff1283cdb6d6c489454dca5f5af16d097e21238c7363358a5
    cnf_sha256=e136e3ec903f8e3166e62de911d1df3aaf98bc8560e673d34d9bb715d9fcde18
    binary_lrat_sha256=dfd06561c88b834ff283924e509ea38934059551729e0a57ff5a5d2badfb487c
    lz4_frame_sha256=127f3babb5de6c783d5564ab5c3c3358f6efbfa42063952db099eb367045edf9
    packed_lz4_sha256=ca6b91b2ff6016ccabb0146b43ac1bf4802b5e6709056f14c2c1f58b7e6368ca
    compact_bytes=1387459294 binary_bytes=620249026
    lz4_frame_bytes=365066606 packed_lz4_bytes=417218979
    source_cnf_clauses=613052 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00085Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨85, by native_decide⟩

private def h1V2P0I00085ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/ca/ca6b91b2ff6016ccabb0146b43ac1bf4802b5e6709056f14c2c1f58b7e6368ca.lrat.lz4p7"

private def h1V2P0I00085RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00085ProofText
    365066606 620249026

private def h1V2P0I00085Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00085Table)
    h1V2P0I00085RawProof).toOption.get!

private theorem h1V2P0I00085Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00085Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00085Table).clauses.toList.all
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
private theorem h1V2P0I00085Check :
    LRAT.check h1V2P0I00085Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00085Table)
        h1V2P0I00085RawProof) := by
  native_decide

theorem h1V2P0I00085Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00085Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00085Nonzero
    h1V2P0I00085RawProof h1V2P0I00085Proof h1V2P0I00085Check

def h1V2P0I00085Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00085Table
  checked := h1V2P0I00085Checked

end Erdos85
