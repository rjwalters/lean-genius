import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=197
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=90 profileIndexed=true rawInventoryTable=true
    orbit=1e0cddae75a672a7
    compact_lrat_sha256=1c2faea60b72385afe0ec8815ec889a8f8670d547d1230c2834b9284efd860b8
    raw_lrat_sha256=1337335d12e62fd00708f3c63aa9c951f5fd33cd4c0808f407daec9cfe75262c
    cnf_sha256=3cbc57eb573e3ed4acaa930544afbb2c1ae33993ab390da6d54103c876722029
    binary_lrat_sha256=ff487b37b8838988d4f06707e18997509b1bdf95bb428252ca7526494f5ac54c
    lz4_frame_sha256=f36d42969e93a2224f4f688b06f0a60f11f63a2c8e65dae3e4d2c98962b157a8
    packed_lz4_sha256=98ffb6785fbfa5f37bbec0105cfa1af3d3fefd97318c6ad132eeadc7c6d2c926
    compact_bytes=1518267647 binary_bytes=668920636
    lz4_frame_bytes=392084890 packed_lz4_bytes=448097018
    source_cnf_clauses=613104 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00197Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨197, by native_decide⟩

private def h1V2P0I00197ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/98/98ffb6785fbfa5f37bbec0105cfa1af3d3fefd97318c6ad132eeadc7c6d2c926.lrat.lz4p7"

private def h1V2P0I00197RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00197ProofText
    392084890 668920636

private def h1V2P0I00197Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00197Table)
    h1V2P0I00197RawProof).toOption.get!

private theorem h1V2P0I00197Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00197Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00197Table).clauses.toList.all
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
private theorem h1V2P0I00197Check :
    LRAT.check h1V2P0I00197Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00197Table)
        h1V2P0I00197RawProof) := by
  native_decide

theorem h1V2P0I00197Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00197Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00197Nonzero
    h1V2P0I00197RawProof h1V2P0I00197Proof h1V2P0I00197Check

def h1V2P0I00197Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00197Table
  checked := h1V2P0I00197Checked

end Erdos85
