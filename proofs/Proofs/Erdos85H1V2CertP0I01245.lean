import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1245
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=495 profileIndexed=true rawInventoryTable=true
    orbit=ceef63d4bce2901d
    compact_lrat_sha256=3ce9945f8da4733a3c457946e39f0bc77bfb816fa2b8e2424c0b763f3449a106
    raw_lrat_sha256=7458897444ba89e9a8567d0a64e4adcc253081126f3aa55ae21f60d20ad939ac
    cnf_sha256=0fbc078f2709a9f1221a0412cd675ee6b9ccb5db67d471c4e1c43efa528c0a2a
    binary_lrat_sha256=d6b1c2d5c6d222a36057b7d53428ff35923dedf663afe3837090a8b5c13a6497
    lz4_frame_sha256=a5b9fad71ce885adfd57259c1896d67a7a6f522bc040a893cce70de750a41fe0
    packed_lz4_sha256=702223da18e40c974823019a3cc52be231e600fa30740e77de4c367878205f5c
    compact_bytes=1371034757 binary_bytes=603312231
    lz4_frame_bytes=345090752 packed_lz4_bytes=394389431
    source_cnf_clauses=613252 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01245Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1245, by native_decide⟩

private def h1V2P0I01245ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/70/702223da18e40c974823019a3cc52be231e600fa30740e77de4c367878205f5c.lrat.lz4p7"

private def h1V2P0I01245RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01245ProofText
    345090752 603312231

private def h1V2P0I01245Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01245Table)
    h1V2P0I01245RawProof).toOption.get!

private theorem h1V2P0I01245Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01245Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01245Table).clauses.toList.all
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
private theorem h1V2P0I01245Check :
    LRAT.check h1V2P0I01245Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01245Table)
        h1V2P0I01245RawProof) := by
  native_decide

theorem h1V2P0I01245Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01245Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01245Nonzero
    h1V2P0I01245RawProof h1V2P0I01245Proof h1V2P0I01245Check

def h1V2P0I01245Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01245Table
  checked := h1V2P0I01245Checked

end Erdos85
