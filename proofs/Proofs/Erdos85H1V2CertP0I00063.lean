import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=63
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=28 profileIndexed=true rawInventoryTable=true
    orbit=096bba0bcaf1e953
    compact_lrat_sha256=fe0ef894e0747ba8a7859663c906e04fe9adf3cd995f8bb4edde3da5be0d18be
    raw_lrat_sha256=461809aae73b8c5f9be05fa19585826e9f56081e35c23057ce140985a97e9e2c
    cnf_sha256=8edaf17f3314a08e30561c44536dd51603960ab8bb21e1c899c044be4900fe86
    binary_lrat_sha256=1bd4b83525944787a60c397376d544d23afcde18081f27b0ec20d9193045fc71
    lz4_frame_sha256=b42febc4a488f99f3ae7289f9ce04141d03eb7cd2487444af6f8e2df91b03156
    packed_lz4_sha256=3acddeb37af10c9c165592dab5bf9b152d1adaef1f2215da1f453e2f2a4bbd49
    compact_bytes=1022906336 binary_bytes=448923884
    lz4_frame_bytes=263216413 packed_lz4_bytes=300818758
    source_cnf_clauses=613204 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00063Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨63, by native_decide⟩

private def h1V2P0I00063ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/3a/3acddeb37af10c9c165592dab5bf9b152d1adaef1f2215da1f453e2f2a4bbd49.lrat.lz4p7"

private def h1V2P0I00063RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00063ProofText
    263216413 448923884

private def h1V2P0I00063Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00063Table)
    h1V2P0I00063RawProof).toOption.get!

private theorem h1V2P0I00063Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00063Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00063Table).clauses.toList.all
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
private theorem h1V2P0I00063Check :
    LRAT.check h1V2P0I00063Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00063Table)
        h1V2P0I00063RawProof) := by
  native_decide

theorem h1V2P0I00063Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00063Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00063Nonzero
    h1V2P0I00063RawProof h1V2P0I00063Proof h1V2P0I00063Check

def h1V2P0I00063Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00063Table
  checked := h1V2P0I00063Checked

end Erdos85
