import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=500
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=199 profileIndexed=true rawInventoryTable=true
    orbit=56091c722daa72c1
    compact_lrat_sha256=2d2a8817ffe55dec43380437e039c2ac1caba77f2583ac5f8d1f606827a92d4c
    raw_lrat_sha256=471423e66dde011fc1f60017eea9fde3f3c0e3c6a4c05dcb87249e6177b10283
    cnf_sha256=7ec05738cf260713e9570fe77cbe3adf14c816642a7c5a2df3752af0d922d2c3
    binary_lrat_sha256=e4f852476d2691c055a37e1e473e32381b3dc67cf7cd2553a65597e6fe1ad0ec
    lz4_frame_sha256=d0f0fcc88c3bbc8b279d172a532b48ac68b255dfb60ba80bdbe901365615b55a
    packed_lz4_sha256=3eb1ffd3da8ef2a28c9f8f047f8b053b7467cd55a71a6f8afd0130f86ba19697
    compact_bytes=606950564 binary_bytes=265466416
    lz4_frame_bytes=153633627 packed_lz4_bytes=175581288
    source_cnf_clauses=613126 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00500Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨500, by native_decide⟩

private def h1V2P0I00500ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/3e/3eb1ffd3da8ef2a28c9f8f047f8b053b7467cd55a71a6f8afd0130f86ba19697.lrat.lz4p7"

private def h1V2P0I00500RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00500ProofText
    153633627 265466416

private def h1V2P0I00500Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00500Table)
    h1V2P0I00500RawProof).toOption.get!

private theorem h1V2P0I00500Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00500Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00500Table).clauses.toList.all
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
private theorem h1V2P0I00500Check :
    LRAT.check h1V2P0I00500Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00500Table)
        h1V2P0I00500RawProof) := by
  native_decide

theorem h1V2P0I00500Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00500Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00500Nonzero
    h1V2P0I00500RawProof h1V2P0I00500Proof h1V2P0I00500Check

def h1V2P0I00500Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00500Table
  checked := h1V2P0I00500Checked

end Erdos85
