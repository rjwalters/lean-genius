import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=116
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=54 profileIndexed=true rawInventoryTable=true
    orbit=11e12e79ceed19f8
    compact_lrat_sha256=bc756c906b5c745493b39a7881b5c802a1538638e4982e22cd2196dbf33e09ae
    raw_lrat_sha256=52a337a87dd183284f9ef66fdd243c15af879d6799d01a546a5f293a87ffd450
    cnf_sha256=ed39b63f8dc1377cd9d6d2d26bcbf142e3813cb129ee30409ed1115d6e7a620d
    binary_lrat_sha256=01b4fe1fc77b9af29082fccfa30bdf8ea95cecb8f22da3c46e14e81f9cbc0675
    lz4_frame_sha256=ebb2aa1e3f334568f507c7ffc5ec54ef9a41da9d99c10de0dd36ce61b7b4fb45
    packed_lz4_sha256=93aa37375d9644b5b3b168a18b6d9178624fcb55f32bbba4e74c9787472af96f
    compact_bytes=957062982 binary_bytes=423205326
    lz4_frame_bytes=242390686 packed_lz4_bytes=277017927
    source_cnf_clauses=613168 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00116Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨116, by native_decide⟩

private def h1V2P0I00116ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/93/93aa37375d9644b5b3b168a18b6d9178624fcb55f32bbba4e74c9787472af96f.lrat.lz4p7"

private def h1V2P0I00116RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00116ProofText
    242390686 423205326

private def h1V2P0I00116Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00116Table)
    h1V2P0I00116RawProof).toOption.get!

private theorem h1V2P0I00116Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00116Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00116Table).clauses.toList.all
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
private theorem h1V2P0I00116Check :
    LRAT.check h1V2P0I00116Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00116Table)
        h1V2P0I00116RawProof) := by
  native_decide

theorem h1V2P0I00116Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00116Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00116Nonzero
    h1V2P0I00116RawProof h1V2P0I00116Proof h1V2P0I00116Check

def h1V2P0I00116Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00116Table
  checked := h1V2P0I00116Checked

end Erdos85
