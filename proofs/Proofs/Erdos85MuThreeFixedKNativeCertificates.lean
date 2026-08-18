import Proofs.Erdos85LratRuntime
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked certificates for the 19 new K-symmetry survivors

The K-symmetry law and finite enumeration reduce the all-triangle and mixed
mu=3 sectors to these eighteen fixed 48-cell grids.  Every instance encodes
the exact row/column hit laws and the C4 common-neighbour bound.  Its LRAT
proof was independently accepted by both drat-trim and the reference
lrat-check implementation before import here.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

private def mu3FixedKCnfText : Fin 19 → String
  | 0 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_0.cnf"
  | 1 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_1.cnf"
  | 2 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_2.cnf"
  | 3 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_3.cnf"
  | 4 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_4.cnf"
  | 5 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_5.cnf"
  | 6 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_6.cnf"
  | 7 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_7.cnf"
  | 8 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_8.cnf"
  | 9 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_9.cnf"
  | 10 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_10.cnf"
  | 11 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_11.cnf"
  | 12 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_12.cnf"
  | 13 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_13.cnf"
  | 14 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_14.cnf"
  | 15 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_15.cnf"
  | 16 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_16.cnf"
  | 17 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_17.cnf"
  | 18 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_18.cnf"
  | _ => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/cnf/fixedk_0.cnf"

private def mu3FixedKProofText : Fin 19 → String
  | 0 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_0.lrat"
  | 1 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_1.lrat"
  | 2 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_2.lrat"
  | 3 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_3.lrat"
  | 4 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_4.lrat"
  | 5 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_5.lrat"
  | 6 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_6.lrat"
  | 7 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_7.lrat"
  | 8 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_8.lrat"
  | 9 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_9.lrat"
  | 10 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_10.lrat"
  | 11 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_11.lrat"
  | 12 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_12.lrat"
  | 13 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_13.lrat"
  | 14 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_14.lrat"
  | 15 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_15.lrat"
  | 16 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_16.lrat"
  | 17 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_17.lrat"
  | 18 => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_18.lrat"
  | _ => include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-fixedk/lrat/fixedk_0.lrat"

/-- The deterministic fixed-K exterior-grid instance at index i. -/
def mu3FixedKCnf (i : Fin 19) : CNF Nat :=
  match DimacsRuntime.parse (mu3FixedKCnfText i).toUTF8 with
  | .ok cnf => cnf
  | .error _ => { clauses := #[] }

private def mu3FixedKRawProof (i : Fin 19) : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof (mu3FixedKProofText i)

private def mu3FixedKProof (i : Fin 19) : Array LRAT.IntAction :=
  (prepareLratProof (mu3FixedKCnf i) (mu3FixedKRawProof i)).toOption.get!

/-- Padding accounts only for fresh variables introduced inside the LRAT
derivation and therefore preserves satisfiability. -/
def mu3FixedKPaddedCnf (i : Fin 19) : CNF Nat :=
  LratExtensionVariables.padCnfForProof (mu3FixedKCnf i)
    (mu3FixedKRawProof i)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem mu3FixedKCheck (i : Fin 19) :
    LRAT.check (mu3FixedKProof i) (mu3FixedKPaddedCnf i) := by
  fin_cases i <;> native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Trusted-checker conclusion for every K-symmetry survivor. -/
theorem mu3FixedKPaddedCnf_unsat (i : Fin 19) :
    (mu3FixedKPaddedCnf i).Unsat :=
  LRAT.check_sound (mu3FixedKProof i) (mu3FixedKPaddedCnf i)
    (mu3FixedKCheck i)

end Erdos85

#print axioms Erdos85.mu3FixedKPaddedCnf_unsat
