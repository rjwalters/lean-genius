import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=74
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=33 profileIndexed=true rawInventoryTable=true
    orbit=0a5c7e9682e74fcf
    compact_lrat_sha256=c6235936cabb8771e4b6b00b415fb532f35fadbfda5c429b227bd0ae38e3d64b
    raw_lrat_sha256=ab061c6702dc026ca235d7d59e659c3a21287a4113cd61ee4b3be33a4f3fd8e3
    cnf_sha256=ab22d9dd680ac40e4a48e2ce918afdc7d37964452ab45b2cc8a799f4c47fae5d
    binary_lrat_sha256=c2cc1b5160534068d6ebc4ca94e103cede3c891287b100f6afa3bcb30d470cb5
    lz4_frame_sha256=3386f4d5ca267aab7cc56f5b160a5ae7a48c68038d62538c5702d7284c166cc0
    packed_lz4_sha256=85b69222079f7b899366a57797978a35a7008effb288876a9ff695b1331a3b55
    compact_bytes=1771896764 binary_bytes=790317389
    lz4_frame_bytes=476900091 packed_lz4_bytes=545028676
    source_cnf_clauses=613140 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00074Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨74, by native_decide⟩

private def h1V2P0I00074ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/85/85b69222079f7b899366a57797978a35a7008effb288876a9ff695b1331a3b55.lrat.lz4p7"

private def h1V2P0I00074RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00074ProofText
    476900091 790317389

private def h1V2P0I00074Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00074Table)
    h1V2P0I00074RawProof).toOption.get!

private theorem h1V2P0I00074Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00074Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00074Table).clauses.toList.all
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
private theorem h1V2P0I00074Check :
    LRAT.check h1V2P0I00074Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00074Table)
        h1V2P0I00074RawProof) := by
  native_decide

theorem h1V2P0I00074Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00074Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00074Nonzero
    h1V2P0I00074RawProof h1V2P0I00074Proof h1V2P0I00074Check

def h1V2P0I00074Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00074Table
  checked := h1V2P0I00074Checked

end Erdos85
