import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1421
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=557 profileIndexed=true rawInventoryTable=true
    orbit=ee2db4a49e0892b3
    compact_lrat_sha256=6ed629b37250dd46edd88a381bb88f93aa17a80cd2803b454df25b86586343c3
    raw_lrat_sha256=c803e05d70c2492bbbe895e552ca0d155c042c51b578f14014d39dea629615f3
    cnf_sha256=973a8f4b7af57cc5c6b6488aabbd2f9a4bd634038ab07a8fb218a54dbf30375f
    binary_lrat_sha256=77a928350e62a30305ff2d1d625cecb6007f0a005a68a427f6d2ed45b87c9cf2
    lz4_frame_sha256=69872afee3e209f881577e42512816962c120bc1696b0f4bb133ced82ac18675
    packed_lz4_sha256=3c45379770e76d5419c6506bb7ad8e2202b183aacba859de9060ffcab595aff5
    compact_bytes=2165234130 binary_bytes=955470512
    lz4_frame_bytes=585857316 packed_lz4_bytes=669551219
    source_cnf_clauses=613256 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01421Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1421, by native_decide⟩

private def h1V2P0I01421ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/3c/3c45379770e76d5419c6506bb7ad8e2202b183aacba859de9060ffcab595aff5.lrat.lz4p7"

private def h1V2P0I01421RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01421ProofText
    585857316 955470512

private def h1V2P0I01421Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01421Table)
    h1V2P0I01421RawProof).toOption.get!

private theorem h1V2P0I01421Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01421Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01421Table).clauses.toList.all
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
private theorem h1V2P0I01421Check :
    LRAT.check h1V2P0I01421Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01421Table)
        h1V2P0I01421RawProof) := by
  native_decide

theorem h1V2P0I01421Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01421Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01421Nonzero
    h1V2P0I01421RawProof h1V2P0I01421Proof h1V2P0I01421Check

def h1V2P0I01421Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01421Table
  checked := h1V2P0I01421Checked

end Erdos85
