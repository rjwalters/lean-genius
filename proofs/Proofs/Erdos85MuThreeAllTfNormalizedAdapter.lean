import Proofs.Erdos85MuThreeAllTfNativeContradiction

/-! # Normalized 48-vertex adapter for the all-triangle-free grid

This file removes raw DIMACS valuations from the graph-facing interface.
An abstract Boolean relation on the unordered pairs of `Fin 48` is read
through the native triangular edge table; a finite lookup theorem certifies
that the table really returns the requested unordered pair.
-/

namespace Erdos85

def mu3NativePairAtId (id : Nat) : Nat × Nat :=
  mu3NativePairs.getD (id - 1) (0, 0)

def mu3NativeEdgeValOfPairRelation
    (adj : (Nat × Nat) → Bool) : DimacsValuation := fun id =>
  adj (mu3NativePairAtId id)

set_option maxRecDepth 100000 in
theorem mu3NativePairAtId_edgeId :
    ∀ u v : Fin 48, u ≠ v →
      mu3NativePairAtId (mu3NativeEdgeId u v) =
        (min u.val v.val, max u.val v.val) := by
  native_decide

theorem mu3NativeEdgeValOfPairRelation_edge
    (adj : (Nat × Nat) → Bool) (u v : Fin 48) (huv : u ≠ v) :
    mu3NativeEdgeValOfPairRelation adj (mu3NativeEdgeId u v) =
      adj (min u.val v.val, max u.val v.val) := by
  simp [mu3NativeEdgeValOfPairRelation, mu3NativePairAtId_edgeId u v huv]

/-- Exact hit-count law, stated on the normalized unordered-pair relation. -/
def Mu3NormalizedHitCounts (shape : Mu3AllTfShape)
    (adj : (Nat × Nat) → Bool) : Prop :=
  ∀ spec ∈ mu3NativeHitSpecs shape,
    seqPrefixTrue
      (mu3NativeVarsRow (mu3NativeEdgeValOfPairRelation adj) spec.1)
      spec.1.size = spec.2

/-- C4 common-neighbor law on the normalized unordered-pair relation. -/
def Mu3NormalizedBaseC4 (adj : (Nat × Nat) → Bool) : Prop :=
  Mu3NativeBaseC4 (mu3NativeEdgeValOfPairRelation adj)

structure Mu3AllTfNormalizedConstraints (shape : Mu3AllTfShape)
    (adj : (Nat × Nat) → Bool) : Prop where
  hitCounts : Mu3NormalizedHitCounts shape adj
  baseC4 : Mu3NormalizedBaseC4 adj

/-- No normalized 48-vertex relation satisfies the all-triangle-free hit and
C4 laws for any of the three component shapes. -/
theorem false_of_mu3AllTfNormalizedConstraints
    (shape : Mu3AllTfShape) (adj : (Nat × Nat) → Bool)
    (h : Mu3AllTfNormalizedConstraints shape adj) : False :=
  false_of_mu3AllTfNativeHitCounts_and_baseC4 shape
    (mu3NativeEdgeValOfPairRelation adj) h.hitCounts h.baseC4

end Erdos85
