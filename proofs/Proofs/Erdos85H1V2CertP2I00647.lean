import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=647
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=12
    orbit=2377d592dee0e405
    compact_lrat_sha256=1cca998b2593f2529e37dccec10c8f65cf2739978fad37145c5ea2723c1a8c8d
    raw_lrat_sha256=665914d99cd1c0f00d37a20417acd428b7f3da94120b43ed31a41a3e638db686
    cnf_sha256=4d242abb60802c051528a16766c768f72a4cfa0f696eb578411bd27b85f40cb8
    binary_lrat_sha256=6d74ab2741019063c2d81fceb0e5c99bf0baca832a69571e923fcbc7b1be83b0
    lz4_frame_sha256=99a1cf638c9162d0e63707cefa1a6eed0a77ec0c8495a9332b37eee48af76123
    packed_lz4_sha256=96267be9f0391a9257d50e9c206fc66ad54c9d9d834dd79ff2e0e2fda3e7ffc8
    compact_bytes=1225049636 binary_bytes=551322918
    lz4_frame_bytes=329013424 packed_lz4_bytes=376015342
    source_cnf_clauses=610200 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00647Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨12, by native_decide⟩

private def h1V2P2I00647ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/96/96267be9f0391a9257d50e9c206fc66ad54c9d9d834dd79ff2e0e2fda3e7ffc8.lrat.lz4p7"

private def h1V2P2I00647RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00647ProofText
    329013424 551322918

private def h1V2P2I00647Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00647Table)
    h1V2P2I00647RawProof).toOption.get!

private theorem h1V2P2I00647Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00647Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00647Table).clauses.toList.all
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
private theorem h1V2P2I00647Check :
    LRAT.check h1V2P2I00647Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00647Table)
        h1V2P2I00647RawProof) := by
  native_decide

theorem h1V2P2I00647Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00647Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00647Nonzero
    h1V2P2I00647RawProof h1V2P2I00647Proof h1V2P2I00647Check

def h1V2P2I00647Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00647Table
  checked := h1V2P2I00647Checked

end Erdos85
