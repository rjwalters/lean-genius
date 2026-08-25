import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=278
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=115 profileIndexed=true rawInventoryTable=true
    orbit=2caebdc55ff6279a
    compact_lrat_sha256=8acf4129033ca223bc49a7eb0223dc428cd2f8caa11e06add3acba921f040c3d
    raw_lrat_sha256=3780470b1b5fbb914a4b0600090bb1ab76ab2068fde11fdcb308e0b1e4c3ac1a
    cnf_sha256=4692d21ce8f76cfe63ad66d1131af956a0aebaf27ef3bb49fdf4cb512de7c201
    binary_lrat_sha256=aad06ae70cbd57a549e2c7dd218c90074e4e7efd0857ffd543857dd6881b8333
    lz4_frame_sha256=c79678b7107088fbf2fc21a45e35f1717a4771135720110fac16b9408d47cc1a
    packed_lz4_sha256=bd51d997435f70972529684940f79bccfbd18291838d232452a89d7c6ce4383a
    compact_bytes=804649373 binary_bytes=354744927
    lz4_frame_bytes=205564733 packed_lz4_bytes=234931124
    source_cnf_clauses=612996 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00278Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨278, by native_decide⟩

private def h1V2P0I00278ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/bd/bd51d997435f70972529684940f79bccfbd18291838d232452a89d7c6ce4383a.lrat.lz4p7"

private def h1V2P0I00278RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00278ProofText
    205564733 354744927

private def h1V2P0I00278Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00278Table)
    h1V2P0I00278RawProof).toOption.get!

private theorem h1V2P0I00278Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00278Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00278Table).clauses.toList.all
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
private theorem h1V2P0I00278Check :
    LRAT.check h1V2P0I00278Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00278Table)
        h1V2P0I00278RawProof) := by
  native_decide

theorem h1V2P0I00278Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00278Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00278Nonzero
    h1V2P0I00278RawProof h1V2P0I00278Proof h1V2P0I00278Check

def h1V2P0I00278Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00278Table
  checked := h1V2P0I00278Checked

end Erdos85
