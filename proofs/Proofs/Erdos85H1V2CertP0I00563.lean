import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=563
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=217 profileIndexed=true rawInventoryTable=true
    orbit=5fb953fd7aeb7c1a
    compact_lrat_sha256=2d9004a50c06fb241488c5b75dfbabd33740f9fc7afdde2548bd8c04ac1b0264
    raw_lrat_sha256=5915ca95ec1a8e95f04290dbe4b081efb7460df1c3e6bc8ca862519451157d97
    cnf_sha256=ca718471d9aa29cd1123881706f2724618843f37e61fb0ee84085790de1d934d
    binary_lrat_sha256=ddeb12955a5e849069278e4c1934518c1155af5fc23e3f6c97cf1b499effff41
    lz4_frame_sha256=b2140ba45ee9c9eee5b8cf55639cec29ceeca733035ec36d77535907f2cbd9e2
    packed_lz4_sha256=be04c4c32c3519277e336a16654bc7ee36690225e930e29b3c8d368ee1d28d5f
    compact_bytes=721506812 binary_bytes=318773359
    lz4_frame_bytes=180349933 packed_lz4_bytes=206114210
    source_cnf_clauses=613038 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00563Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨563, by native_decide⟩

private def h1V2P0I00563ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/be/be04c4c32c3519277e336a16654bc7ee36690225e930e29b3c8d368ee1d28d5f.lrat.lz4p7"

private def h1V2P0I00563RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00563ProofText
    180349933 318773359

private def h1V2P0I00563Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00563Table)
    h1V2P0I00563RawProof).toOption.get!

private theorem h1V2P0I00563Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00563Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00563Table).clauses.toList.all
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
private theorem h1V2P0I00563Check :
    LRAT.check h1V2P0I00563Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00563Table)
        h1V2P0I00563RawProof) := by
  native_decide

theorem h1V2P0I00563Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00563Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00563Nonzero
    h1V2P0I00563RawProof h1V2P0I00563Proof h1V2P0I00563Check

def h1V2P0I00563Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00563Table
  checked := h1V2P0I00563Checked

end Erdos85
