import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=345
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=150 profileIndexed=true rawInventoryTable=true
    orbit=399e0ec0a6e44d42
    compact_lrat_sha256=db2f8f0976667f6422e61a455fc2be9c035cda8866635be8a1f55f89e2c74636
    raw_lrat_sha256=6a5746beae3d98ae35fef613140931ea9e367c7f3ede1e85bf3512179d5bace9
    cnf_sha256=2ce80fc55130f6509506eb69669bc05894c537e11373b1a7b7e6cf620e8130d0
    binary_lrat_sha256=b67073bbb51d5f9d6ff098745280b4917012e50d9abde23b2bfa6843e2c226f0
    lz4_frame_sha256=8bcc02a662603d220b8e9e47fe0a6676abbd5ca2e815efe1222d721c00d33808
    packed_lz4_sha256=10e1051202835f47ea3d7b1381f328f6ab1992a280066e9fa898c3c4d466b9ca
    compact_bytes=318273595 binary_bytes=139960751
    lz4_frame_bytes=80772050 packed_lz4_bytes=92310915
    source_cnf_clauses=612996 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00345Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨345, by native_decide⟩

private def h1V2P0I00345ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/10/10e1051202835f47ea3d7b1381f328f6ab1992a280066e9fa898c3c4d466b9ca.lrat.lz4p7"

private def h1V2P0I00345RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00345ProofText
    80772050 139960751

private def h1V2P0I00345Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00345Table)
    h1V2P0I00345RawProof).toOption.get!

private theorem h1V2P0I00345Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00345Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00345Table).clauses.toList.all
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
private theorem h1V2P0I00345Check :
    LRAT.check h1V2P0I00345Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00345Table)
        h1V2P0I00345RawProof) := by
  native_decide

theorem h1V2P0I00345Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00345Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00345Nonzero
    h1V2P0I00345RawProof h1V2P0I00345Proof h1V2P0I00345Check

def h1V2P0I00345Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00345Table
  checked := h1V2P0I00345Checked

end Erdos85
