import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=669
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=266 profileIndexed=true rawInventoryTable=true
    orbit=7270de1d28b4d05c
    compact_lrat_sha256=7d124bcce6e6f519ccc15d1400d55fc14e53641de01a0aff57ae9ab2c48a0625
    raw_lrat_sha256=df3b0936aabb350b1dcd013490d5f94b47e9774a1211511d67327ccdec82fc21
    cnf_sha256=ee52ee44d82a2cf067cc8b846405c754f938a9d91ba5924a34d6f82273274e4b
    binary_lrat_sha256=888f59b085195cf22480cd65bfe36b5394c8d048d19d3b798679580f4d2aa0bb
    lz4_frame_sha256=f8557dbc6d93a03d66f57b3aeb8a9dae9ec559f5f661d517e6b947385c65b930
    packed_lz4_sha256=4b8ffd219fbd04301935ad2aecaf5b2051a527a1ed5a18d7afc930abd3610eb9
    compact_bytes=961288918 binary_bytes=421192460
    lz4_frame_bytes=250780439 packed_lz4_bytes=286606216
    source_cnf_clauses=613188 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00669Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨669, by native_decide⟩

private def h1V2P0I00669ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/4b/4b8ffd219fbd04301935ad2aecaf5b2051a527a1ed5a18d7afc930abd3610eb9.lrat.lz4p7"

private def h1V2P0I00669RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00669ProofText
    250780439 421192460

private def h1V2P0I00669Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00669Table)
    h1V2P0I00669RawProof).toOption.get!

private theorem h1V2P0I00669Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00669Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00669Table).clauses.toList.all
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
private theorem h1V2P0I00669Check :
    LRAT.check h1V2P0I00669Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00669Table)
        h1V2P0I00669RawProof) := by
  native_decide

theorem h1V2P0I00669Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00669Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00669Nonzero
    h1V2P0I00669RawProof h1V2P0I00669Proof h1V2P0I00669Check

def h1V2P0I00669Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00669Table
  checked := h1V2P0I00669Checked

end Erdos85
