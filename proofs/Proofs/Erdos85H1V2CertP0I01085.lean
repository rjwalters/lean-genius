import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1085
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=431 profileIndexed=true rawInventoryTable=true
    orbit=b647301779568a1a
    compact_lrat_sha256=4fa11ad683750a213f4f45ee934284f582cfb72af3276ef62800936c8fba5155
    raw_lrat_sha256=aea03f5956f330a212c48e3c71aba8f4cad1e9c6b08651cb7c73e043164fedfc
    cnf_sha256=31e25e094efaa557ce575afaa2c9e49cf1ab0fa6ab0bb8a4a38b90213398679a
    binary_lrat_sha256=31c9b4ce9815694046c5da8ddb5ae1e6536229885123bd3eb8da2d1fdab5aa9f
    lz4_frame_sha256=d73dc86a6fc1affeaa65381e532e90daa2b1e218faa2f06f50c943bd41feec47
    packed_lz4_sha256=b5545d8c42be0194919d186948ac5a08c711a79c7a11c44c1cf62ce1e08747fb
    compact_bytes=287332709 binary_bytes=125243353
    lz4_frame_bytes=71470224 packed_lz4_bytes=81680256
    source_cnf_clauses=613080 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01085Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1085, by native_decide⟩

private def h1V2P0I01085ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b5/b5545d8c42be0194919d186948ac5a08c711a79c7a11c44c1cf62ce1e08747fb.lrat.lz4p7"

private def h1V2P0I01085RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01085ProofText
    71470224 125243353

private def h1V2P0I01085Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01085Table)
    h1V2P0I01085RawProof).toOption.get!

private theorem h1V2P0I01085Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01085Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01085Table).clauses.toList.all
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
private theorem h1V2P0I01085Check :
    LRAT.check h1V2P0I01085Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01085Table)
        h1V2P0I01085RawProof) := by
  native_decide

theorem h1V2P0I01085Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01085Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01085Nonzero
    h1V2P0I01085RawProof h1V2P0I01085Proof h1V2P0I01085Check

def h1V2P0I01085Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01085Table
  checked := h1V2P0I01085Checked

end Erdos85
