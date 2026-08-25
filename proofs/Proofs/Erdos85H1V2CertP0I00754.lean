import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=754
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=303 profileIndexed=true rawInventoryTable=true
    orbit=803caaed653bc936
    compact_lrat_sha256=2ad73cf1c811c9ca369b914b7fd34bc556f07b67051f6dada930b5ce746a110d
    raw_lrat_sha256=d26c742a7e024c77a5646800214d56e5426aae11fdadd4bf5e944a46c46d1ac6
    cnf_sha256=7ab4a3da0042dc9e6b54dd0ce34f8ac9240abe18d6c133794f0366e8c33a221d
    binary_lrat_sha256=a2ce581033987bd5b760550efac63d892e88ae9104d24b9d7a201f0c751685af
    lz4_frame_sha256=ac7f10b848a720a4629dea855b2f1d88101f1dfb8faf41272fa532e17168033e
    packed_lz4_sha256=b1926534a5eaea6f27b7aaf1c1efa37caf2245d35c92fe821a303feec868517c
    compact_bytes=708010754 binary_bytes=310225145
    lz4_frame_bytes=173040853 packed_lz4_bytes=197760975
    source_cnf_clauses=613140 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00754Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨754, by native_decide⟩

private def h1V2P0I00754ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b1/b1926534a5eaea6f27b7aaf1c1efa37caf2245d35c92fe821a303feec868517c.lrat.lz4p7"

private def h1V2P0I00754RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00754ProofText
    173040853 310225145

private def h1V2P0I00754Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00754Table)
    h1V2P0I00754RawProof).toOption.get!

private theorem h1V2P0I00754Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00754Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00754Table).clauses.toList.all
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
private theorem h1V2P0I00754Check :
    LRAT.check h1V2P0I00754Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00754Table)
        h1V2P0I00754RawProof) := by
  native_decide

theorem h1V2P0I00754Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00754Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00754Nonzero
    h1V2P0I00754RawProof h1V2P0I00754Proof h1V2P0I00754Check

def h1V2P0I00754Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00754Table
  checked := h1V2P0I00754Checked

end Erdos85
