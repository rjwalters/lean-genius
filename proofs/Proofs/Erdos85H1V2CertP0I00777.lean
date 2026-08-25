import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=777
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=312 profileIndexed=true rawInventoryTable=true
    orbit=83bbdf03b3097e85
    compact_lrat_sha256=1ccab53a415f219e1fce3f92603c9002553f06fef814b0240c422517257a9fdc
    raw_lrat_sha256=5dbec30d5161cbdd37379b7dcecd9592c8c8bc9075efe5c38d4e351ee734902b
    cnf_sha256=e0e06ec74dcf2a2e7513207c2f40ecb58c6e1c5983d7fea0a5d6269526a28b31
    binary_lrat_sha256=80ab7e5a0f0c9737f34d2abbe1ae1c51b5ea8f6d7428ceba2f17721fc70fd8a0
    lz4_frame_sha256=93b67252c56c9898c9920bb29c65272bc28bc4d8eb8b87d1f392ab3e054b1576
    packed_lz4_sha256=a959d8b05e8e970b8e0419b1799033b4395f4d29d2002599b6e58750e09b9a9f
    compact_bytes=519190674 binary_bytes=228111684
    lz4_frame_bytes=135082625 packed_lz4_bytes=154380143
    source_cnf_clauses=613228 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00777Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨777, by native_decide⟩

private def h1V2P0I00777ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/a9/a959d8b05e8e970b8e0419b1799033b4395f4d29d2002599b6e58750e09b9a9f.lrat.lz4p7"

private def h1V2P0I00777RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00777ProofText
    135082625 228111684

private def h1V2P0I00777Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00777Table)
    h1V2P0I00777RawProof).toOption.get!

private theorem h1V2P0I00777Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00777Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00777Table).clauses.toList.all
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
private theorem h1V2P0I00777Check :
    LRAT.check h1V2P0I00777Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00777Table)
        h1V2P0I00777RawProof) := by
  native_decide

theorem h1V2P0I00777Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00777Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00777Nonzero
    h1V2P0I00777RawProof h1V2P0I00777Proof h1V2P0I00777Check

def h1V2P0I00777Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00777Table
  checked := h1V2P0I00777Checked

end Erdos85
