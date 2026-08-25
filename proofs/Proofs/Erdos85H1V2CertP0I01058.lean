import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1058
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=417 profileIndexed=true rawInventoryTable=true
    orbit=b2b19e71d279f92a
    compact_lrat_sha256=0710d25bca9fa0aaf2f041d37db2306181fc55cd40b59e2a4a6fa664d955dc82
    raw_lrat_sha256=62fdf155e66d2e79fb081ed5d515805c719a95801140c9a0c45ff2789c86ed76
    cnf_sha256=c113079b6d56734158d0a2ee4782ccee58efcadf67763d05b22bb541c9c759d3
    binary_lrat_sha256=d6823d0881479019b5fe97a3fd42cafc49a9aa51ffada382c1546526f90c0107
    lz4_frame_sha256=181ade6c949e6bdf6c4cf16a7c181f256516ae763286aabfb5921508aa29cd4b
    packed_lz4_sha256=98e52d3d661148b5b9c4d0840350cb15615d96b54b6ea3e0b3fce64ff4eacbf4
    compact_bytes=715431652 binary_bytes=314365810
    lz4_frame_bytes=186248495 packed_lz4_bytes=212855423
    source_cnf_clauses=613138 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01058Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1058, by native_decide⟩

private def h1V2P0I01058ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/98/98e52d3d661148b5b9c4d0840350cb15615d96b54b6ea3e0b3fce64ff4eacbf4.lrat.lz4p7"

private def h1V2P0I01058RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01058ProofText
    186248495 314365810

private def h1V2P0I01058Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01058Table)
    h1V2P0I01058RawProof).toOption.get!

private theorem h1V2P0I01058Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01058Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01058Table).clauses.toList.all
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
private theorem h1V2P0I01058Check :
    LRAT.check h1V2P0I01058Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01058Table)
        h1V2P0I01058RawProof) := by
  native_decide

theorem h1V2P0I01058Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01058Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01058Nonzero
    h1V2P0I01058RawProof h1V2P0I01058Proof h1V2P0I01058Check

def h1V2P0I01058Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01058Table
  checked := h1V2P0I01058Checked

end Erdos85
