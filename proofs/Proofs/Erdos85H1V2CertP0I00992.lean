import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=992
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=391 profileIndexed=true rawInventoryTable=true
    orbit=a78d2764b4914a80
    compact_lrat_sha256=5c43c2020be03961f2fc386dd5e9abd3ff6f440cf94870d25ee00cc3c2edcb39
    raw_lrat_sha256=97fc5f5855807af862877c5f29b107bf22b41a85097c9b3f969fd82fc94253a1
    cnf_sha256=e4c1bc718607f15ac7796f89dd43a0ebd66804340684386dbbb95a2e2788d84a
    binary_lrat_sha256=42e1466626ac302027df0e2c54f575400282e088a97227a04c39fa77993e0e5f
    lz4_frame_sha256=6bf92b9d33735ef4325a58466d810d6fde7d0935860023eddba0216c822c8d4e
    packed_lz4_sha256=314e96535a3abd846140cd127884dc88d6718541c14228733468893ab22ab249
    compact_bytes=888188472 binary_bytes=392987192
    lz4_frame_bytes=228627181 packed_lz4_bytes=261288207
    source_cnf_clauses=613108 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00992Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨992, by native_decide⟩

private def h1V2P0I00992ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/31/314e96535a3abd846140cd127884dc88d6718541c14228733468893ab22ab249.lrat.lz4p7"

private def h1V2P0I00992RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00992ProofText
    228627181 392987192

private def h1V2P0I00992Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00992Table)
    h1V2P0I00992RawProof).toOption.get!

private theorem h1V2P0I00992Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00992Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00992Table).clauses.toList.all
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
private theorem h1V2P0I00992Check :
    LRAT.check h1V2P0I00992Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00992Table)
        h1V2P0I00992RawProof) := by
  native_decide

theorem h1V2P0I00992Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00992Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00992Nonzero
    h1V2P0I00992RawProof h1V2P0I00992Proof h1V2P0I00992Check

def h1V2P0I00992Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00992Table
  checked := h1V2P0I00992Checked

end Erdos85
