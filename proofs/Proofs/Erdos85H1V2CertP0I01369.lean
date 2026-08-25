import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1369
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=538 profileIndexed=true rawInventoryTable=true
    orbit=e4af8e1abed2a70e
    compact_lrat_sha256=1888c4980b615da5d1b6602c333cc374e3a2922117d5782d4058bb81569e3343
    raw_lrat_sha256=3044c2ad226486b662bfa3afbc3d967b6a70601e36c34c83d18f327d5d1ddaf9
    cnf_sha256=33d0745cd8f8876fe569e19149b623affe7ccbde099aaac7371b5581183c0825
    binary_lrat_sha256=a46216eaf4637338cb71967681415792a03a05947141dc2726d8ff153545cdee
    lz4_frame_sha256=37e515a3c14c0015cf1f2c6aac52babbbe72cbb434db0e338729aff64a68a9d2
    packed_lz4_sha256=52ec5c4279a116853d3a89357facf4f2c21a79b2a4cd8dd163d9392b8ecf9617
    compact_bytes=1564954619 binary_bytes=692733833
    lz4_frame_bytes=407173252 packed_lz4_bytes=465340860
    source_cnf_clauses=613044 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01369Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1369, by native_decide⟩

private def h1V2P0I01369ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/52/52ec5c4279a116853d3a89357facf4f2c21a79b2a4cd8dd163d9392b8ecf9617.lrat.lz4p7"

private def h1V2P0I01369RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01369ProofText
    407173252 692733833

private def h1V2P0I01369Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01369Table)
    h1V2P0I01369RawProof).toOption.get!

private theorem h1V2P0I01369Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01369Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01369Table).clauses.toList.all
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
private theorem h1V2P0I01369Check :
    LRAT.check h1V2P0I01369Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01369Table)
        h1V2P0I01369RawProof) := by
  native_decide

theorem h1V2P0I01369Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01369Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01369Nonzero
    h1V2P0I01369RawProof h1V2P0I01369Proof h1V2P0I01369Check

def h1V2P0I01369Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01369Table
  checked := h1V2P0I01369Checked

end Erdos85
