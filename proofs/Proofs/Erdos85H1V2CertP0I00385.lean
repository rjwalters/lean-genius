import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=385
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=161 profileIndexed=true rawInventoryTable=true
    orbit=4182045ae8701eba
    compact_lrat_sha256=99690d6441df67d60d54081b9960649609cdf96fdb8be0748f721d717b6e5dcb
    raw_lrat_sha256=17ba3bfa4f6a45b996764a9b67512ce8b1bd0c1ac32d063303d789d04fa72c95
    cnf_sha256=5f164d3dd6865361daafc2dec216cb05be83e6348963e05944b946e822df4561
    binary_lrat_sha256=e80cb48cb98af25e5cd9249daa1e10b1e650529e598e4b36945a317d311fa077
    lz4_frame_sha256=849a2c54d8375bc945c7dd3de7679eff19ea392582b32d86a753d3adb5762787
    packed_lz4_sha256=6cfc7f646a1726b09f544ba177d28c843f59d3bfb74f21821f1b5e2ae1a53d9f
    compact_bytes=836645047 binary_bytes=367912986
    lz4_frame_bytes=223647644 packed_lz4_bytes=255597308
    source_cnf_clauses=613116 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00385Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨385, by native_decide⟩

private def h1V2P0I00385ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/6c/6cfc7f646a1726b09f544ba177d28c843f59d3bfb74f21821f1b5e2ae1a53d9f.lrat.lz4p7"

private def h1V2P0I00385RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00385ProofText
    223647644 367912986

private def h1V2P0I00385Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00385Table)
    h1V2P0I00385RawProof).toOption.get!

private theorem h1V2P0I00385Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00385Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00385Table).clauses.toList.all
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
private theorem h1V2P0I00385Check :
    LRAT.check h1V2P0I00385Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00385Table)
        h1V2P0I00385RawProof) := by
  native_decide

theorem h1V2P0I00385Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00385Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00385Nonzero
    h1V2P0I00385RawProof h1V2P0I00385Proof h1V2P0I00385Check

def h1V2P0I00385Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00385Table
  checked := h1V2P0I00385Checked

end Erdos85
