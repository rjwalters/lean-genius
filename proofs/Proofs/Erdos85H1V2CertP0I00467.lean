import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=467
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=186 profileIndexed=true rawInventoryTable=true
    orbit=50e25c86511ed1e7
    compact_lrat_sha256=d1c0bfd4334820c704be61b2cbab0e69278bb554fab1498dc65ed04a63f3e0f4
    raw_lrat_sha256=cce225c9ce325c90eb1fb5b5aa17ed3323de26342f3f905ca3a191339ad6f0cf
    cnf_sha256=1b8413ce9083e8467078450324b0077381e21a8ed1d3498690f2644ed3d7b9c2
    binary_lrat_sha256=41f5805165647495edc113672b356dd1faf89389625c2cc32d52bb868dad3144
    lz4_frame_sha256=67a54a77b3f9a22e0db3a601f65b8170f8b646cc33a7ad9b5ffee3b333d2cde9
    packed_lz4_sha256=86d639a658108bb861766a2e7fc880bb7a9a0533e70b8f18bffc15c9fbb42c15
    compact_bytes=989187590 binary_bytes=434870246
    lz4_frame_bytes=248249402 packed_lz4_bytes=283713603
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00467Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨467, by native_decide⟩

private def h1V2P0I00467ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/86/86d639a658108bb861766a2e7fc880bb7a9a0533e70b8f18bffc15c9fbb42c15.lrat.lz4p7"

private def h1V2P0I00467RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00467ProofText
    248249402 434870246

private def h1V2P0I00467Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00467Table)
    h1V2P0I00467RawProof).toOption.get!

private theorem h1V2P0I00467Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00467Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00467Table).clauses.toList.all
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
private theorem h1V2P0I00467Check :
    LRAT.check h1V2P0I00467Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00467Table)
        h1V2P0I00467RawProof) := by
  native_decide

theorem h1V2P0I00467Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00467Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00467Nonzero
    h1V2P0I00467RawProof h1V2P0I00467Proof h1V2P0I00467Check

def h1V2P0I00467Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00467Table
  checked := h1V2P0I00467Checked

end Erdos85
