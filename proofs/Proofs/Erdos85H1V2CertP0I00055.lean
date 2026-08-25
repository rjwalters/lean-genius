import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=55
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=25 profileIndexed=true rawInventoryTable=true
    orbit=07e064c7982e270f
    compact_lrat_sha256=d5394dd9c7f7375abb3052542e45c0f7c7b0cae16047c506daeeb399f2008047
    raw_lrat_sha256=afe9d16d2d6a4be9cd3a31b03d6480670f773cd08355fa681ec09c37e9ac2ea6
    cnf_sha256=7ee83e0cb56c266317cac957fd9568f443c630de1d43f6479eaf668b29593007
    binary_lrat_sha256=1e26a2a1236875ec76b0236d2a6d5c1527f8648c02de6683e70df7fb2dda136d
    lz4_frame_sha256=40ce3a3185b8ce08b49b4f2594a2c20b3ef0ad77fe130953279f63c2d06e808b
    packed_lz4_sha256=094537ce2b314364d981de556d2509c5b206d6ec221050e4a197e8ec63b399d2
    compact_bytes=1897539270 binary_bytes=843293901
    lz4_frame_bytes=497900344 packed_lz4_bytes=569028965
    source_cnf_clauses=613072 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00055Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨55, by native_decide⟩

private def h1V2P0I00055ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/09/094537ce2b314364d981de556d2509c5b206d6ec221050e4a197e8ec63b399d2.lrat.lz4p7"

private def h1V2P0I00055RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00055ProofText
    497900344 843293901

private def h1V2P0I00055Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00055Table)
    h1V2P0I00055RawProof).toOption.get!

private theorem h1V2P0I00055Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00055Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00055Table).clauses.toList.all
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
private theorem h1V2P0I00055Check :
    LRAT.check h1V2P0I00055Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00055Table)
        h1V2P0I00055RawProof) := by
  native_decide

theorem h1V2P0I00055Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00055Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00055Nonzero
    h1V2P0I00055RawProof h1V2P0I00055Proof h1V2P0I00055Check

def h1V2P0I00055Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00055Table
  checked := h1V2P0I00055Checked

end Erdos85
