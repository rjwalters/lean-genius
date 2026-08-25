import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1098
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=436 profileIndexed=true rawInventoryTable=true
    orbit=b8fa929ded877f2e
    compact_lrat_sha256=20789ca86c0dbbbe6ed2dfe900ab19c5872515e6664d6a26307d199c40c2052d
    raw_lrat_sha256=dd0b002e25bd7353f42fee81e44c37358fe2db561c941cd883f2513338408aa6
    cnf_sha256=4311adfa0d0b22f26efd583e40d486a0421bedf6864cf55308355a06f3c3fc96
    binary_lrat_sha256=417659b4135311923f38c3a5ec6172c729e75f0ce90853277cc6a99d1772eef9
    lz4_frame_sha256=123c73eefd6b1fc96b3786d349bc1e91052f1d66797e3aed1ab26fff2a699877
    packed_lz4_sha256=46a88e50d53c6162a58ae4492ffa2d3d3f9ba9e95539724769d129a7fb7bfad1
    compact_bytes=1505581443 binary_bytes=665358281
    lz4_frame_bytes=400310592 packed_lz4_bytes=457497820
    source_cnf_clauses=613104 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01098Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1098, by native_decide⟩

private def h1V2P0I01098ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/46/46a88e50d53c6162a58ae4492ffa2d3d3f9ba9e95539724769d129a7fb7bfad1.lrat.lz4p7"

private def h1V2P0I01098RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01098ProofText
    400310592 665358281

private def h1V2P0I01098Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01098Table)
    h1V2P0I01098RawProof).toOption.get!

private theorem h1V2P0I01098Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01098Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01098Table).clauses.toList.all
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
private theorem h1V2P0I01098Check :
    LRAT.check h1V2P0I01098Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01098Table)
        h1V2P0I01098RawProof) := by
  native_decide

theorem h1V2P0I01098Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01098Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01098Nonzero
    h1V2P0I01098RawProof h1V2P0I01098Proof h1V2P0I01098Check

def h1V2P0I01098Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01098Table
  checked := h1V2P0I01098Checked

end Erdos85
