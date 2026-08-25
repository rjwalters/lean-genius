import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=736
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=292 profileIndexed=true rawInventoryTable=true
    orbit=7c653627c5a260a7
    compact_lrat_sha256=fca98471cfbac0198c0ca1f76ff186dd3230dbd00098d807a08be46d38b0997e
    raw_lrat_sha256=ec1fbcf1035608dd60ce4dbcfd925c143cc4053b68f4d82ad54cda8fcde4c36c
    cnf_sha256=ebbe7592f8cad43304709c6d9f26d845e6a02059061bfedd34d1558c6e89021f
    binary_lrat_sha256=1bfd7a1a2ec374fe70e43307414aa91ff2de1ff3b685e2b57bb24ac70be50024
    lz4_frame_sha256=9d060bb2b1ee0668dc07c8299a01ecbf5f54c85ff6535eaf55a857ddf5063c8f
    packed_lz4_sha256=fb339008642bcdecddcb5a660787b8dc73ea2662262cbc21ef93c00b68149cf1
    compact_bytes=473482702 binary_bytes=207428877
    lz4_frame_bytes=122834462 packed_lz4_bytes=140382243
    source_cnf_clauses=613216 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00736Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨736, by native_decide⟩

private def h1V2P0I00736ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/fb/fb339008642bcdecddcb5a660787b8dc73ea2662262cbc21ef93c00b68149cf1.lrat.lz4p7"

private def h1V2P0I00736RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00736ProofText
    122834462 207428877

private def h1V2P0I00736Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00736Table)
    h1V2P0I00736RawProof).toOption.get!

private theorem h1V2P0I00736Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00736Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00736Table).clauses.toList.all
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
private theorem h1V2P0I00736Check :
    LRAT.check h1V2P0I00736Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00736Table)
        h1V2P0I00736RawProof) := by
  native_decide

theorem h1V2P0I00736Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00736Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00736Nonzero
    h1V2P0I00736RawProof h1V2P0I00736Proof h1V2P0I00736Check

def h1V2P0I00736Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00736Table
  checked := h1V2P0I00736Checked

end Erdos85
