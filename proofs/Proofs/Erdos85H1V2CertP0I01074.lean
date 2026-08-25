import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1074
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=425 profileIndexed=true rawInventoryTable=true
    orbit=b515f2f6f89447a8
    compact_lrat_sha256=6ffe5341a4a9d09c344b5ade161c69eed0f1f8431f63ce9d26baa908dde4dddb
    raw_lrat_sha256=20bf2c130b5b550201307b0f9cef150b1e1fbd0fe5747819fe15d699e2312ab9
    cnf_sha256=ff7ee456ce1e0cfb9a051f058aa31d4d4a665e7458852e3ec531734ea3278fb8
    binary_lrat_sha256=ee85b7d4eb24cb0fff03a0cf737d8f887379c41ea6e70dd6a56cb7d5fb0dd764
    lz4_frame_sha256=75495f21bb30c4a228ed703ad8e6a0034b0c474dce134bfc55bb33cb1f1183c0
    packed_lz4_sha256=fccf39010196b7e00f7d919a1b5fca36cde34000624debe9def4ded1f7b93279
    compact_bytes=1140137937 binary_bytes=504320389
    lz4_frame_bytes=292893629 packed_lz4_bytes=334735576
    source_cnf_clauses=613070 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01074Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1074, by native_decide⟩

private def h1V2P0I01074ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/fc/fccf39010196b7e00f7d919a1b5fca36cde34000624debe9def4ded1f7b93279.lrat.lz4p7"

private def h1V2P0I01074RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01074ProofText
    292893629 504320389

private def h1V2P0I01074Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01074Table)
    h1V2P0I01074RawProof).toOption.get!

private theorem h1V2P0I01074Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01074Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01074Table).clauses.toList.all
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
private theorem h1V2P0I01074Check :
    LRAT.check h1V2P0I01074Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01074Table)
        h1V2P0I01074RawProof) := by
  native_decide

theorem h1V2P0I01074Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01074Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01074Nonzero
    h1V2P0I01074RawProof h1V2P0I01074Proof h1V2P0I01074Check

def h1V2P0I01074Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01074Table
  checked := h1V2P0I01074Checked

end Erdos85
