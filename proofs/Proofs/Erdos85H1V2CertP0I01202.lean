import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1202
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=477 profileIndexed=true rawInventoryTable=true
    orbit=c865a0d1c69ee2ea
    compact_lrat_sha256=706c3ff71d5b523fe8d90493967ad80073064ede83dcab0a4292ee38e146b835
    raw_lrat_sha256=fad61cf88fc7864e5ef55064ee93832079e9da78ed1266ab0867b3fa60c21c0b
    cnf_sha256=b1e15947a115b8f9559efd34382edb3007f0170797247d33d629477701da678a
    binary_lrat_sha256=3615f7764c79b73c8eecac7639e8364b1d021850ce3849935e5bd1c85eba0840
    lz4_frame_sha256=f739a3dde0345e31bde3c08f3d4dcbcfbcb12b4f6273c8e7c93d668984b9cc8b
    packed_lz4_sha256=ce9f67d70579a757803f29907bd54c69f580037f743f7607fcb38f357d18f008
    compact_bytes=1839514884 binary_bytes=812249273
    lz4_frame_bytes=503449788 packed_lz4_bytes=575371187
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01202Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1202, by native_decide⟩

private def h1V2P0I01202ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/ce/ce9f67d70579a757803f29907bd54c69f580037f743f7607fcb38f357d18f008.lrat.lz4p7"

private def h1V2P0I01202RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01202ProofText
    503449788 812249273

private def h1V2P0I01202Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01202Table)
    h1V2P0I01202RawProof).toOption.get!

private theorem h1V2P0I01202Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01202Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01202Table).clauses.toList.all
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
private theorem h1V2P0I01202Check :
    LRAT.check h1V2P0I01202Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01202Table)
        h1V2P0I01202RawProof) := by
  native_decide

theorem h1V2P0I01202Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01202Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01202Nonzero
    h1V2P0I01202RawProof h1V2P0I01202Proof h1V2P0I01202Check

def h1V2P0I01202Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01202Table
  checked := h1V2P0I01202Checked

end Erdos85
