import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=903
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=362 profileIndexed=true rawInventoryTable=true
    orbit=97c6c04e2f35b6bb
    compact_lrat_sha256=9f19be7bccc8fa30e7a34cd01e1503dc39cece3683f3df3bc73bbec800c21f0d
    raw_lrat_sha256=58fe69aa07c2528da99377a579ffdf35b38ff839e62231eafcf90c1913273f1a
    cnf_sha256=eb48e5c8b7864586f374bbc0893698cafb23c2b3727e662eecea80426a589fea
    binary_lrat_sha256=b6bcc5e39811fd3172fa2deed9f5c67e168998e69531237b04fa714dd4f820eb
    lz4_frame_sha256=f4040f667c8940085daad3b33ae5c7e4d2d329aac28ad6685ce505cebf5b7342
    packed_lz4_sha256=9e0cf65162f80805085344d0692b4cb0c7e7b1824de5af73f8b235cc7ab1a475
    compact_bytes=872842672 binary_bytes=386716109
    lz4_frame_bytes=224443900 packed_lz4_bytes=256507315
    source_cnf_clauses=613024 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00903Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨903, by native_decide⟩

private def h1V2P0I00903ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/9e/9e0cf65162f80805085344d0692b4cb0c7e7b1824de5af73f8b235cc7ab1a475.lrat.lz4p7"

private def h1V2P0I00903RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00903ProofText
    224443900 386716109

private def h1V2P0I00903Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00903Table)
    h1V2P0I00903RawProof).toOption.get!

private theorem h1V2P0I00903Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00903Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00903Table).clauses.toList.all
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
private theorem h1V2P0I00903Check :
    LRAT.check h1V2P0I00903Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00903Table)
        h1V2P0I00903RawProof) := by
  native_decide

theorem h1V2P0I00903Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00903Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00903Nonzero
    h1V2P0I00903RawProof h1V2P0I00903Proof h1V2P0I00903Check

def h1V2P0I00903Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00903Table
  checked := h1V2P0I00903Checked

end Erdos85
