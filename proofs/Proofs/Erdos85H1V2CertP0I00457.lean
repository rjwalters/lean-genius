import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=457
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=182 profileIndexed=true rawInventoryTable=true
    orbit=4f8c77620fd809e0
    compact_lrat_sha256=35d40bab67d1eecfec04334c6b566564cae9f174ca007a6d09d6292d2750ab84
    raw_lrat_sha256=8ac317eb74dca014ae2df9f3a1618d0f2e6ffaffd43eff4a942bbdcb5e9498c3
    cnf_sha256=b277c9ff7c2fafc2dea161c4cdf7ac93abda3ddf724c87f1e81d924fde94bcba
    binary_lrat_sha256=be0ed95947ac666a8a582f1e203f5c4a69fae0fa6b0e0b63c16f2b2da325e7ae
    lz4_frame_sha256=8e500e3df8392543894755831643ce1977d007ae41396cf48b518e9b2bb3a98e
    packed_lz4_sha256=98c9563ae78896876208ed073aee9a31887f51e2e828d2227cef569be65ad685
    compact_bytes=1569443941 binary_bytes=693737569
    lz4_frame_bytes=414015677 packed_lz4_bytes=473160774
    source_cnf_clauses=613172 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00457Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨457, by native_decide⟩

private def h1V2P0I00457ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/98/98c9563ae78896876208ed073aee9a31887f51e2e828d2227cef569be65ad685.lrat.lz4p7"

private def h1V2P0I00457RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00457ProofText
    414015677 693737569

private def h1V2P0I00457Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00457Table)
    h1V2P0I00457RawProof).toOption.get!

private theorem h1V2P0I00457Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00457Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00457Table).clauses.toList.all
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
private theorem h1V2P0I00457Check :
    LRAT.check h1V2P0I00457Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00457Table)
        h1V2P0I00457RawProof) := by
  native_decide

theorem h1V2P0I00457Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00457Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00457Nonzero
    h1V2P0I00457RawProof h1V2P0I00457Proof h1V2P0I00457Check

def h1V2P0I00457Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00457Table
  checked := h1V2P0I00457Checked

end Erdos85
