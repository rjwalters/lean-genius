import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=594
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=231 profileIndexed=true rawInventoryTable=true
    orbit=65308a9bb3be8fcd
    compact_lrat_sha256=b7c655da3b69d7c0d84c988521625cfb1417c376b93e7db7da0ccb80fe5eb13f
    raw_lrat_sha256=995667789f209b8d1d9387d74fd75fb79b5ac87c4ce219a7a0505bb2414d55df
    cnf_sha256=ddb65a7c6d4704f4123d33cc5bd941b62ec137dfa89545e80a94a05aa7250d39
    binary_lrat_sha256=4d605135a63f2ae73a1fe3974b5a04e17b8ce6d3c90b2a9ce59176d956887c76
    lz4_frame_sha256=d628bd027bf7b2eb6aed6dfc06ae8e9248989236c4c8a48ddf6353bf499e9c46
    packed_lz4_sha256=5a7f2d455d198938c6c38f09497620557c1895eb76296f5db0887bb0dd4c4932
    compact_bytes=1750560286 binary_bytes=778231977
    lz4_frame_bytes=453022108 packed_lz4_bytes=517739552
    source_cnf_clauses=613124 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00594Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨594, by native_decide⟩

private def h1V2P0I00594ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/5a/5a7f2d455d198938c6c38f09497620557c1895eb76296f5db0887bb0dd4c4932.lrat.lz4p7"

private def h1V2P0I00594RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00594ProofText
    453022108 778231977

private def h1V2P0I00594Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00594Table)
    h1V2P0I00594RawProof).toOption.get!

private theorem h1V2P0I00594Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00594Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00594Table).clauses.toList.all
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
private theorem h1V2P0I00594Check :
    LRAT.check h1V2P0I00594Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00594Table)
        h1V2P0I00594RawProof) := by
  native_decide

theorem h1V2P0I00594Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00594Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00594Nonzero
    h1V2P0I00594RawProof h1V2P0I00594Proof h1V2P0I00594Check

def h1V2P0I00594Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00594Table
  checked := h1V2P0I00594Checked

end Erdos85
