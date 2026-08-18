import Proofs.Erdos85MuThreeAllTfNativeCnfSemantics
import Proofs.Erdos85MuThreeAllTfNativeNonzero

/-! # Static contradiction for the native all-triangle-free grid CNFs -/

namespace Erdos85

/-- Final Boolean interface to the checked certificates.  All encoding and
DIMACS side conditions have been discharged; callers provide only the exact
row/column hit counts and the C4 common-neighbor bound on base edge bits. -/
theorem false_of_mu3AllTfNativeHitCounts_and_baseC4
    (shape : Mu3AllTfShape) (edgeVal : DimacsValuation)
    (hhitCounts : ∀ spec ∈ mu3NativeHitSpecs shape,
      seqPrefixTrue (mu3NativeVarsRow edgeVal spec.1) spec.1.size = spec.2)
    (hbaseC4 : Mu3NativeBaseC4 edgeVal) : False :=
  false_of_mu3AllTfNativeStaticConstraints shape edgeVal
    (mu3NativeFinalState_clauses_nonzero shape) hhitCounts hbaseC4

end Erdos85
