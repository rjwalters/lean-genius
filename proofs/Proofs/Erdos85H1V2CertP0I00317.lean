import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=317
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=134 profileIndexed=true rawInventoryTable=true
    orbit=341ef82248614b93
    compact_lrat_sha256=61bca82fee46058ec545b1069345da9380c6d581406e3cf365ca9237ba2dd758
    raw_lrat_sha256=c2bf1614cbafec270d4872997598f3eeebfd00016c95c83ec7e44af878707288
    cnf_sha256=0a098f99aab5f3a2d44f198af9adb503ff50580d78d84a0fb2c0253c6dc2b0bc
    binary_lrat_sha256=778f7d4de3f29b168fe3b6c8d9e3181dabdee36b427cb8bab65c2b8637da2c47
    lz4_frame_sha256=f34f46e7b952f938ee9555ed5caae3149055b3f9a430e88b598a49b2ac9a9ccd
    packed_lz4_sha256=08ee1c19a801ecc9fac4c9afe72719fe45de71b5658f063bbb13fbdc1dd73719
    compact_bytes=1040584726 binary_bytes=460848444
    lz4_frame_bytes=251831203 packed_lz4_bytes=287807090
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00317Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨317, by native_decide⟩

private def h1V2P0I00317ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/08/08ee1c19a801ecc9fac4c9afe72719fe45de71b5658f063bbb13fbdc1dd73719.lrat.lz4p7"

private def h1V2P0I00317RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00317ProofText
    251831203 460848444

private def h1V2P0I00317Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00317Table)
    h1V2P0I00317RawProof).toOption.get!

private theorem h1V2P0I00317Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00317Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00317Table).clauses.toList.all
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
private theorem h1V2P0I00317Check :
    LRAT.check h1V2P0I00317Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00317Table)
        h1V2P0I00317RawProof) := by
  native_decide

theorem h1V2P0I00317Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00317Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00317Nonzero
    h1V2P0I00317RawProof h1V2P0I00317Proof h1V2P0I00317Check

def h1V2P0I00317Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00317Table
  checked := h1V2P0I00317Checked

end Erdos85
