import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=76
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=34 profileIndexed=true rawInventoryTable=true
    orbit=0aea569cb4772b51
    compact_lrat_sha256=3fd73831ed46d1d745d42a65b1909271852f9e2067234168b35fd2f3c1e0b052
    raw_lrat_sha256=bf7084de7790511defe5b6bcdffc1cb8d3c0aefacf1141f647a59fed0ff9d81b
    cnf_sha256=d1c09870a9e0eb11e31b1f92863cd2235ddfd26601c8cb4acda105396bce277d
    binary_lrat_sha256=20cd6abc60796165c8229aeed8f01e9740d06bedf52e2aff9e955cc1c1f3dd20
    lz4_frame_sha256=8703b407d1bc4f594fa333c6410916f31439564330f2ab32e8eed4ee493c3ba9
    packed_lz4_sha256=e199cd6370eb160df8aeb5a9caef53a4eda0b7cef7dba190a26e37673f6f4d1b
    compact_bytes=1287525142 binary_bytes=570714860
    lz4_frame_bytes=341660490 packed_lz4_bytes=390469132
    source_cnf_clauses=613164 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00076Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨76, by native_decide⟩

private def h1V2P0I00076ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/e1/e199cd6370eb160df8aeb5a9caef53a4eda0b7cef7dba190a26e37673f6f4d1b.lrat.lz4p7"

private def h1V2P0I00076RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00076ProofText
    341660490 570714860

private def h1V2P0I00076Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00076Table)
    h1V2P0I00076RawProof).toOption.get!

private theorem h1V2P0I00076Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00076Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00076Table).clauses.toList.all
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
private theorem h1V2P0I00076Check :
    LRAT.check h1V2P0I00076Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00076Table)
        h1V2P0I00076RawProof) := by
  native_decide

theorem h1V2P0I00076Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00076Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00076Nonzero
    h1V2P0I00076RawProof h1V2P0I00076Proof h1V2P0I00076Check

def h1V2P0I00076Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00076Table
  checked := h1V2P0I00076Checked

end Erdos85
