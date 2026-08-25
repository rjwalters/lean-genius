import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=171
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=80 profileIndexed=true rawInventoryTable=true
    orbit=1a38399376e7447f
    compact_lrat_sha256=2d6c3492330b115c8f32156565f2c8de7e534b7e6475af8041e55f7a6d3a26d8
    raw_lrat_sha256=2f640469d9ab613c0ec0cb2a11dc41cf1ab0b400ce6ff0385f1d6862e323df79
    cnf_sha256=126591876658a7c470620bc71de587b3e1fe1538330691abed95291431c4b4cd
    binary_lrat_sha256=746ea0c822107d110b02cec039c07781c9c100c661ef1dad6d3908069c7acb46
    lz4_frame_sha256=93c4047d94790170c6fbed54cf85264ab1cfcc2b77db2f5d59fee32b4de465b9
    packed_lz4_sha256=33cdb43b622c4878cc1ca685708c964a7aeba3d21a437504eb88572f1b2fca9c
    compact_bytes=1626315775 binary_bytes=722869574
    lz4_frame_bytes=417625103 packed_lz4_bytes=477285832
    source_cnf_clauses=613228 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00171Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨171, by native_decide⟩

private def h1V2P0I00171ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/33/33cdb43b622c4878cc1ca685708c964a7aeba3d21a437504eb88572f1b2fca9c.lrat.lz4p7"

private def h1V2P0I00171RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00171ProofText
    417625103 722869574

private def h1V2P0I00171Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00171Table)
    h1V2P0I00171RawProof).toOption.get!

private theorem h1V2P0I00171Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00171Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00171Table).clauses.toList.all
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
private theorem h1V2P0I00171Check :
    LRAT.check h1V2P0I00171Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00171Table)
        h1V2P0I00171RawProof) := by
  native_decide

theorem h1V2P0I00171Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00171Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00171Nonzero
    h1V2P0I00171RawProof h1V2P0I00171Proof h1V2P0I00171Check

def h1V2P0I00171Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00171Table
  checked := h1V2P0I00171Checked

end Erdos85
