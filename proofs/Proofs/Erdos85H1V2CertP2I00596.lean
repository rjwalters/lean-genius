import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=596
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=11
    orbit=2050932681822300
    compact_lrat_sha256=6b4336ee035608133e4d98970a2572b02b8747b10b2a97f7fbd62421773f449d
    raw_lrat_sha256=3ed2c6e7f62ada29375975be5e0d4926e8d9d3ee7134ee3af8e391e5e555067e
    cnf_sha256=17e2f03fe5b9ef900c2360183de6ed4822310c389d001560485f9d73a751a9aa
    binary_lrat_sha256=79d7a81aefef7a24a6f8330c83da279ec1550a1bd7ca88441bbabe6cbbf243b1
    lz4_frame_sha256=cde54908eb941b20f0b24f841274910aa48594bc70b893f3634f1151b5958c81
    packed_lz4_sha256=48e32a04d6c9ab920f780d264788857e7d6fc286c42fdda69012e1811d438433
    compact_bytes=1045278732 binary_bytes=470193849
    lz4_frame_bytes=281553038 packed_lz4_bytes=321774901
    source_cnf_clauses=610232 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00596Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨11, by native_decide⟩

private def h1V2P2I00596ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/48/48e32a04d6c9ab920f780d264788857e7d6fc286c42fdda69012e1811d438433.lrat.lz4p7"

private def h1V2P2I00596RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00596ProofText
    281553038 470193849

private def h1V2P2I00596Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00596Table)
    h1V2P2I00596RawProof).toOption.get!

private theorem h1V2P2I00596Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00596Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00596Table).clauses.toList.all
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
private theorem h1V2P2I00596Check :
    LRAT.check h1V2P2I00596Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00596Table)
        h1V2P2I00596RawProof) := by
  native_decide

theorem h1V2P2I00596Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00596Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00596Nonzero
    h1V2P2I00596RawProof h1V2P2I00596Proof h1V2P2I00596Check

def h1V2P2I00596Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00596Table
  checked := h1V2P2I00596Checked

end Erdos85
