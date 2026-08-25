import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=564
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=218 profileIndexed=true rawInventoryTable=true
    orbit=5fc4225ac8f37d0e
    compact_lrat_sha256=a6fd948ab327a64ecea708a8dd25e52c08763f3a5059f6fe0b9d648fa4a81f6a
    raw_lrat_sha256=2c6ba73bf44079fcd3264c590dff916b90fdd08cef73ae98271432950e99a657
    cnf_sha256=9696fd0aa502171ae5d8740a7f73c3493e83affb7abaa285c908894fa3fdde8a
    binary_lrat_sha256=3bc25b9a3b3d6da2ce405743d38ca2e633a1cc2a07d826e7d54f1dade498556a
    lz4_frame_sha256=4979c8ce7b188de864710299dee57fd89273f64510db6b93fbe088b433614844
    packed_lz4_sha256=2794648025f08f9ee134452266bdf405ecb5de0106b51a968e370237816e710d
    compact_bytes=1817102655 binary_bytes=801439812
    lz4_frame_bytes=463424475 packed_lz4_bytes=529627972
    source_cnf_clauses=613036 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00564Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨564, by native_decide⟩

private def h1V2P0I00564ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/27/2794648025f08f9ee134452266bdf405ecb5de0106b51a968e370237816e710d.lrat.lz4p7"

private def h1V2P0I00564RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00564ProofText
    463424475 801439812

private def h1V2P0I00564Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00564Table)
    h1V2P0I00564RawProof).toOption.get!

private theorem h1V2P0I00564Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00564Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00564Table).clauses.toList.all
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
private theorem h1V2P0I00564Check :
    LRAT.check h1V2P0I00564Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00564Table)
        h1V2P0I00564RawProof) := by
  native_decide

theorem h1V2P0I00564Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00564Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00564Nonzero
    h1V2P0I00564RawProof h1V2P0I00564Proof h1V2P0I00564Check

def h1V2P0I00564Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00564Table
  checked := h1V2P0I00564Checked

end Erdos85
