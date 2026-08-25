import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=923
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=367 profileIndexed=true rawInventoryTable=true
    orbit=9bdfb597b3af4b30
    compact_lrat_sha256=1f9ae8dfd780c89be58e1438418fc5f42c3826fdd17f1c1d83b78c3e28b8398a
    raw_lrat_sha256=ec96d45b6f484149415ebe4fcd7ef6a33c3bea63c1871d38edd1f7c1603d1f90
    cnf_sha256=eb970fe00f8333f25dc8ff1eb3ecf0fe642c570d33ad8183b452a827756d008f
    binary_lrat_sha256=b20c1bb8303c7dbac872437b45c29562e853bc0d3706e8caa5a4a6a907207e86
    lz4_frame_sha256=ff27b14bedc36e139364bab388656ee51c39c508fac22433f694a55cae351675
    packed_lz4_sha256=55e44b134e519ca8b33ab49d6a1c3458bb8d3387674492d22bec627be441d74e
    compact_bytes=1488999764 binary_bytes=658122203
    lz4_frame_bytes=370762649 packed_lz4_bytes=423728742
    source_cnf_clauses=613154 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00923Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨923, by native_decide⟩

private def h1V2P0I00923ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/55/55e44b134e519ca8b33ab49d6a1c3458bb8d3387674492d22bec627be441d74e.lrat.lz4p7"

private def h1V2P0I00923RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00923ProofText
    370762649 658122203

private def h1V2P0I00923Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00923Table)
    h1V2P0I00923RawProof).toOption.get!

private theorem h1V2P0I00923Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00923Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00923Table).clauses.toList.all
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
private theorem h1V2P0I00923Check :
    LRAT.check h1V2P0I00923Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00923Table)
        h1V2P0I00923RawProof) := by
  native_decide

theorem h1V2P0I00923Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00923Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00923Nonzero
    h1V2P0I00923RawProof h1V2P0I00923Proof h1V2P0I00923Check

def h1V2P0I00923Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00923Table
  checked := h1V2P0I00923Checked

end Erdos85
