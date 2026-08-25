import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1184
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=469 profileIndexed=true rawInventoryTable=true
    orbit=c59055eb2859903f
    compact_lrat_sha256=518271dbe69d381bb7cbfb15c2abce469aeb285bd210f7927023604ccf999ae9
    raw_lrat_sha256=527a46813ea65e28a58e9817f67dde60e5e877afceca1b885154e296f832cdf3
    cnf_sha256=cc2245931b0d2563204b5e40c83cb5bee306a49ba8195c364b0726ebccceaea0
    binary_lrat_sha256=c8c007dcc776c4d2578a224a941432495773d74ab87a6f279d19d08a978f221e
    lz4_frame_sha256=bb03e66079725d59e69b0c24ad645220aa3b16fb86e095c98afbadd36a34f27e
    packed_lz4_sha256=7d2e751e1186ab8a48d5b9a26e654d5a7ab3bf8e895a1076f2156d1635482522
    compact_bytes=2259969224 binary_bytes=1007783867
    lz4_frame_bytes=583750577 packed_lz4_bytes=667143517
    source_cnf_clauses=613228 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01184Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1184, by native_decide⟩

private def h1V2P0I01184ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/7d/7d2e751e1186ab8a48d5b9a26e654d5a7ab3bf8e895a1076f2156d1635482522.lrat.lz4p7"

private def h1V2P0I01184RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01184ProofText
    583750577 1007783867

private def h1V2P0I01184Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01184Table)
    h1V2P0I01184RawProof).toOption.get!

private theorem h1V2P0I01184Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01184Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01184Table).clauses.toList.all
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
private theorem h1V2P0I01184Check :
    LRAT.check h1V2P0I01184Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01184Table)
        h1V2P0I01184RawProof) := by
  native_decide

theorem h1V2P0I01184Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01184Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01184Nonzero
    h1V2P0I01184RawProof h1V2P0I01184Proof h1V2P0I01184Check

def h1V2P0I01184Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01184Table
  checked := h1V2P0I01184Checked

end Erdos85
