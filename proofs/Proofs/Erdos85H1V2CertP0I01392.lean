import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1392
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=545 profileIndexed=true rawInventoryTable=true
    orbit=ea51dab0cb28b3b0
    compact_lrat_sha256=f8dcd76e7870e2cd64c1692562a9d4093c8c252f07ad275807f5cb419f718c48
    raw_lrat_sha256=f419412808797235f21b3b405deb57890aa8afed5830c5b8b1ad5c45d2662731
    cnf_sha256=2c5fe4acbd48f9b2a20ba8db54531592997fadca241bd06a9dad10e524385145
    binary_lrat_sha256=b90fb108860ae149bb527c15111380945a679d741a86c4ca4b21625aa295974b
    lz4_frame_sha256=fc5b3079af1ab86561dd56a2c57776bce40e6f8c04f3e8affe968675ac6265ac
    packed_lz4_sha256=51ccdeacbc600548cd8dae56e97cf26a77d17f1bb18a980d242441950e9d92be
    compact_bytes=1634283293 binary_bytes=719132423
    lz4_frame_bytes=433720666 packed_lz4_bytes=495680762
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01392Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1392, by native_decide⟩

private def h1V2P0I01392ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/51/51ccdeacbc600548cd8dae56e97cf26a77d17f1bb18a980d242441950e9d92be.lrat.lz4p7"

private def h1V2P0I01392RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01392ProofText
    433720666 719132423

private def h1V2P0I01392Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01392Table)
    h1V2P0I01392RawProof).toOption.get!

private theorem h1V2P0I01392Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01392Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01392Table).clauses.toList.all
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
private theorem h1V2P0I01392Check :
    LRAT.check h1V2P0I01392Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01392Table)
        h1V2P0I01392RawProof) := by
  native_decide

theorem h1V2P0I01392Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01392Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01392Nonzero
    h1V2P0I01392RawProof h1V2P0I01392Proof h1V2P0I01392Check

def h1V2P0I01392Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01392Table
  checked := h1V2P0I01392Checked

end Erdos85
