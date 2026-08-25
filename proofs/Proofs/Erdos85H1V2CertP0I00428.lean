import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=428
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=173 profileIndexed=true rawInventoryTable=true
    orbit=4ad2e9bfd88c40df
    compact_lrat_sha256=4208c9ceb02971bfb798979c889dba06882fe2097cc84a0fb89c430fbf3c89d3
    raw_lrat_sha256=e15aa2ac666c5498249d4a9a3d1e8ae602d344ababe234d3bc1ce71e7202405f
    cnf_sha256=c6cc629ccee09b5a3aa0bea0fa33871f6f7990732feaf762a42a33be90acc579
    binary_lrat_sha256=8bb8c04a5208a8e407e1d068b7b062be477829cc52b96ad13155310764639678
    lz4_frame_sha256=fa7089bbc51016a97f8081ddc6254dfa30bb4842ecbfff68702f733352cb513c
    packed_lz4_sha256=87c9c850de5c6be9cbd7a264073477d92edfd4d98f9cb57d187a61c470fc9c0c
    compact_bytes=2019006786 binary_bytes=894287130
    lz4_frame_bytes=511146698 packed_lz4_bytes=584167655
    source_cnf_clauses=613142 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00428Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨428, by native_decide⟩

private def h1V2P0I00428ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/87/87c9c850de5c6be9cbd7a264073477d92edfd4d98f9cb57d187a61c470fc9c0c.lrat.lz4p7"

private def h1V2P0I00428RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00428ProofText
    511146698 894287130

private def h1V2P0I00428Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00428Table)
    h1V2P0I00428RawProof).toOption.get!

private theorem h1V2P0I00428Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00428Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00428Table).clauses.toList.all
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
private theorem h1V2P0I00428Check :
    LRAT.check h1V2P0I00428Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00428Table)
        h1V2P0I00428RawProof) := by
  native_decide

theorem h1V2P0I00428Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00428Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00428Nonzero
    h1V2P0I00428RawProof h1V2P0I00428Proof h1V2P0I00428Check

def h1V2P0I00428Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00428Table
  checked := h1V2P0I00428Checked

end Erdos85
