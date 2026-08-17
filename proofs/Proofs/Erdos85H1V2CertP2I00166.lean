import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=166
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=3
    orbit=085aec8f3ea88536
    compact_lrat_sha256=c5d46892d41ca46ec8ade752d7d6048c3b997430b8d98066e8083205b9e75a91
    raw_lrat_sha256=f2f64e1fff7aadae2c729b65b9b53a12e3444f2df27fc9c0976491ab45c018d3
    cnf_sha256=a9a1934fd7d3f0e6e87c337706b5fd733ea53702b073024047f3480610039bf7
    binary_lrat_sha256=3f49f93da834ee31917c4b4d6dab0ab80148102c469773bc9a032521f6996c98
    lz4_frame_sha256=ac49cb6e8276b5d80e866522a0b8830278d2da7def04b101a67ab1ce18a97163
    packed_lz4_sha256=c0410fc14460ae120d3f2b0a3d64727d01a7cc4570f98c8ce3b5aa5910ebf576
    compact_bytes=1479423407 binary_bytes=668807816
    lz4_frame_bytes=397028921 packed_lz4_bytes=453747339
    source_cnf_clauses=610420 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00166Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨3, by native_decide⟩

private def h1V2P2I00166ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/c0/c0410fc14460ae120d3f2b0a3d64727d01a7cc4570f98c8ce3b5aa5910ebf576.lrat.lz4p7"

private def h1V2P2I00166RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00166ProofText
    397028921 668807816

private def h1V2P2I00166Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00166Table)
    h1V2P2I00166RawProof).toOption.get!

private theorem h1V2P2I00166Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00166Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00166Table).clauses.toList.all
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
private theorem h1V2P2I00166Check :
    LRAT.check h1V2P2I00166Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00166Table)
        h1V2P2I00166RawProof) := by
  native_decide

theorem h1V2P2I00166Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00166Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00166Nonzero
    h1V2P2I00166RawProof h1V2P2I00166Proof h1V2P2I00166Check

def h1V2P2I00166Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00166Table
  checked := h1V2P2I00166Checked

end Erdos85
