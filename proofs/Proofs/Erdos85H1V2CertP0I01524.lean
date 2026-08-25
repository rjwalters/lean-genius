import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1524
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=607 profileIndexed=true rawInventoryTable=true
    orbit=fe1b5c8c1a502158
    compact_lrat_sha256=471b193b421ba00327725cd066b58ec3b8d79d98dd120548c756d3655025afd5
    raw_lrat_sha256=9fb23919419de4c5af88b5b4b18919a4e82fc73fd38bfddfddfd1e378328c88f
    cnf_sha256=78fc85e595c0117d74af746489e78ee3b224d2c16445b17e9a040b5aada21fa0
    binary_lrat_sha256=674bac91a9a20463215c81f07cd049c86728922b350e81ceaa8f7774c5145f40
    lz4_frame_sha256=100d5630eb1400da92ea3d27fddb23917f2424ef077f780703923374adcef85a
    packed_lz4_sha256=15f7af3efcfa251fce7870b87134fd56ffe72f715c1f23b02933a25c1f3d259c
    compact_bytes=1234514415 binary_bytes=542111701
    lz4_frame_bytes=309898432 packed_lz4_bytes=354169637
    source_cnf_clauses=613108 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01524Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1524, by native_decide⟩

private def h1V2P0I01524ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/15/15f7af3efcfa251fce7870b87134fd56ffe72f715c1f23b02933a25c1f3d259c.lrat.lz4p7"

private def h1V2P0I01524RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01524ProofText
    309898432 542111701

private def h1V2P0I01524Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01524Table)
    h1V2P0I01524RawProof).toOption.get!

private theorem h1V2P0I01524Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01524Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01524Table).clauses.toList.all
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
private theorem h1V2P0I01524Check :
    LRAT.check h1V2P0I01524Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01524Table)
        h1V2P0I01524RawProof) := by
  native_decide

theorem h1V2P0I01524Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01524Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01524Nonzero
    h1V2P0I01524RawProof h1V2P0I01524Proof h1V2P0I01524Check

def h1V2P0I01524Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01524Table
  checked := h1V2P0I01524Checked

end Erdos85
