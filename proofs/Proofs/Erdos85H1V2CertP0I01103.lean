import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1103
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=438 profileIndexed=true rawInventoryTable=true
    orbit=b953a73b0e372480
    compact_lrat_sha256=19ea021a6325da47d7d9513ce9533e22531decfe08ace14438222d62a601c1b6
    raw_lrat_sha256=cd7ab105cfcdba49f63f47d4341aec4847114538903cc437882fe7e4227ce28a
    cnf_sha256=07d61f0f4afb98a4925bcc9f0833cdf7da7fdc5ac905c5298586bb65e0c6eaa2
    binary_lrat_sha256=1230aea2f0641c28f2cebe981470308899af972d194cb8c49c92c87f71ce21ac
    lz4_frame_sha256=2271818dc11d4a7d5db6a9564f66f628b1025d970811d8a4880af3bac47bc2c1
    packed_lz4_sha256=a059d4244ca3831be9a35c98a6909b3c49ed7496f4ca781eb1979499a0d4fa9e
    compact_bytes=468738691 binary_bytes=204875041
    lz4_frame_bytes=118683729 packed_lz4_bytes=135638548
    source_cnf_clauses=613046 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01103Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1103, by native_decide⟩

private def h1V2P0I01103ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/a0/a059d4244ca3831be9a35c98a6909b3c49ed7496f4ca781eb1979499a0d4fa9e.lrat.lz4p7"

private def h1V2P0I01103RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01103ProofText
    118683729 204875041

private def h1V2P0I01103Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01103Table)
    h1V2P0I01103RawProof).toOption.get!

private theorem h1V2P0I01103Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01103Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01103Table).clauses.toList.all
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
private theorem h1V2P0I01103Check :
    LRAT.check h1V2P0I01103Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01103Table)
        h1V2P0I01103RawProof) := by
  native_decide

theorem h1V2P0I01103Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01103Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01103Nonzero
    h1V2P0I01103RawProof h1V2P0I01103Proof h1V2P0I01103Check

def h1V2P0I01103Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01103Table
  checked := h1V2P0I01103Checked

end Erdos85
