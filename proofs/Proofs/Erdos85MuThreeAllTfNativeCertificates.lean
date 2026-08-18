import Proofs.Erdos85MuThreeAllTfNativeCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighV2ExtensionCertificate

/-! # Checked native LRAT certificates for the all-tf `mu = 3` grid

Each packed proof is replayed by Lean's standard LRAT checker against the CNF
constructed by `mu3AllTfNativeSatCnf` inside Lean.
-/

namespace Erdos85

open Std.Tactic.BVDecide

private def mu3NativeC16ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-cayley-sidon/mu3grid/native-certificates/mu3-native-C16.binary.lrat.lz4p7"

private def mu3NativeC16Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof mu3NativeC16ProofText 1141664 1553366

private def mu3NativeC10C6ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-cayley-sidon/mu3grid/native-certificates/mu3-native-C10C6.binary.lrat.lz4p7"

private def mu3NativeC10C6Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof mu3NativeC10C6ProofText 949097 1281631

private def mu3NativeC8C8ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-cayley-sidon/mu3grid/native-certificates/mu3-native-C8C8.binary.lrat.lz4p7"

private def mu3NativeC8C8Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof mu3NativeC8C8ProofText 741835 991321

private def mu3PrepareProof (shape : Mu3AllTfShape)
    (proof : Array LRAT.IntAction) : Array LRAT.IntAction :=
  match prepareLratProof (mu3AllTfNativeSatCnf shape) proof with
  | .ok prepared => prepared
  | .error _ => #[]

private def mu3NativeC16Prepared : Array LRAT.IntAction :=
  mu3PrepareProof .c16 mu3NativeC16Proof

private def mu3NativeC10C6Prepared : Array LRAT.IntAction :=
  mu3PrepareProof .c10c6 mu3NativeC10C6Proof

private def mu3NativeC8C8Prepared : Array LRAT.IntAction :=
  mu3PrepareProof .c8c8 mu3NativeC8C8Proof

theorem mu3NativeProof_sizes :
    mu3NativeC16Proof.size = 8482 ∧
      mu3NativeC10C6Proof.size = 7621 ∧
      mu3NativeC8C8Proof.size = 5829 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem mu3NativeC16_check :
    LRAT.check mu3NativeC16Prepared
      (LratExtensionVariables.padCnfForProof
        (mu3AllTfNativeSatCnf .c16) mu3NativeC16Proof) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem mu3NativeC10C6_check :
    LRAT.check mu3NativeC10C6Prepared
      (LratExtensionVariables.padCnfForProof
        (mu3AllTfNativeSatCnf .c10c6) mu3NativeC10C6Proof) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem mu3NativeC8C8_check :
    LRAT.check mu3NativeC8C8Prepared
      (LratExtensionVariables.padCnfForProof
        (mu3AllTfNativeSatCnf .c8c8) mu3NativeC8C8Proof) := by
  native_decide

theorem mu3AllTfNativeC16_unsat : (mu3AllTfNativeSatCnf .c16).Unsat :=
  cnf_unsat_of_padCnfForProof_unsat _ mu3NativeC16Proof
    (LRAT.check_sound mu3NativeC16Prepared _ mu3NativeC16_check)

theorem mu3AllTfNativeC10C6_unsat : (mu3AllTfNativeSatCnf .c10c6).Unsat :=
  cnf_unsat_of_padCnfForProof_unsat _ mu3NativeC10C6Proof
    (LRAT.check_sound mu3NativeC10C6Prepared _ mu3NativeC10C6_check)

theorem mu3AllTfNativeC8C8_unsat : (mu3AllTfNativeSatCnf .c8c8).Unsat :=
  cnf_unsat_of_padCnfForProof_unsat _ mu3NativeC8C8Proof
    (LRAT.check_sound mu3NativeC8C8Prepared _ mu3NativeC8C8_check)

end Erdos85
