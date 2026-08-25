import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1236
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=488 profileIndexed=true rawInventoryTable=true
    orbit=cd91fc344fa62a12
    compact_lrat_sha256=ba487d92776c748126b36701a7ff5a64e20dbc87d885e7eaf6a82bb897cdab9e
    raw_lrat_sha256=e9180cec63482f535ea1a6339015f57979165b25c10a9351e67ce25fc8db1949
    cnf_sha256=d5f9314c99b72901d604831f9899e8d655a7ec38fc14e17fc8a3e21936193f79
    binary_lrat_sha256=6dd3167440a4e76386cb5955a77ba48a159982100170f34a506fb656d3cb5ae8
    lz4_frame_sha256=fb9c15676400f22d7571b6cb8f0e0dbd4f9b631f8a00dcd07d90441468c26276
    packed_lz4_sha256=0d82ab922f457f5373ae5ab63fdc88b70622c6dd4a8d6b4f514de79f5c0bad00
    compact_bytes=1303304149 binary_bytes=572673632
    lz4_frame_bytes=336103454 packed_lz4_bytes=384118234
    source_cnf_clauses=613188 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01236Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1236, by native_decide⟩

private def h1V2P0I01236ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/0d/0d82ab922f457f5373ae5ab63fdc88b70622c6dd4a8d6b4f514de79f5c0bad00.lrat.lz4p7"

private def h1V2P0I01236RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01236ProofText
    336103454 572673632

private def h1V2P0I01236Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01236Table)
    h1V2P0I01236RawProof).toOption.get!

private theorem h1V2P0I01236Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01236Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01236Table).clauses.toList.all
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
private theorem h1V2P0I01236Check :
    LRAT.check h1V2P0I01236Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01236Table)
        h1V2P0I01236RawProof) := by
  native_decide

theorem h1V2P0I01236Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01236Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01236Nonzero
    h1V2P0I01236RawProof h1V2P0I01236Proof h1V2P0I01236Check

def h1V2P0I01236Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01236Table
  checked := h1V2P0I01236Checked

end Erdos85
