import Proofs.Erdos85MuThreeFixedKNativeCnf
import Proofs.Erdos85MuThreeAllTfNativeCnfSemantics

/-!
# Parametric hit semantics for fixed-K native CNFs

The old semantic engine is generic below its three-shape hit-specification
wrapper.  This module supplies the corresponding wrapper for arbitrary
`Mu3NativeGridSpec` data and reuses the already-proved sequential-counter
soundness induction unchanged.
-/

namespace Erdos85

set_option maxRecDepth 100000

/-- Row and column exact-cardinality blocks for an arbitrary ordered
48-cell grid.  Their order is exactly the native generator order. -/
def mu3GridHitSpecs (grid : Mu3NativeGridSpec) : List Mu3NativeCardSpec :=
  (List.range 48).flatMap fun u =>
    let cell := grid.cells.getD u 0
    let xu := cell / 8
    let yu := cell % 8
    (List.range 8).map (fun x =>
      (mu3GridRowVars grid u x,
        if grid.internal x yu then 0 else 1)) ++
    (List.range 8).map (fun y =>
      (mu3GridColumnVars grid u y,
        if grid.internal xu y then 0 else 1))

/-- Generic hit-prefix satisfiability.  The hypotheses mention only fixed
base-ID facts and the graph-derived exact row/column counts. -/
theorem mu3GridHitSpecs_formulaSatisfiable
    (grid : Mu3NativeGridSpec) (edgeVal : DimacsValuation)
    (hnonzero : ∀ spec ∈ mu3GridHitSpecs grid,
      ∀ lit ∈ spec.1, lit ≠ 0)
    (hbaseBound : ∀ spec ∈ mu3GridHitSpecs grid,
      ∀ lit ∈ spec.1, lit.natAbs ≤ 1128)
    (hcounts : ∀ spec ∈ mu3GridHitSpecs grid,
      seqPrefixTrue (mu3NativeVarsRow edgeVal spec.1) spec.1.size = spec.2) :
    ∃ val,
      dimacsFormulaSatisfied val
        (mu3NativeRunExactSpecs (mu3GridHitSpecs grid) {}).clauses ∧
      dimacsFormulaBounded
        (mu3NativeRunExactSpecs (mu3GridHitSpecs grid) {}).top
        (mu3NativeRunExactSpecs (mu3GridHitSpecs grid) {}).clauses ∧
      ∀ id, id ≤ 1128 → val id = edgeVal id := by
  let out := mu3NativeRunExactSpecsVal edgeVal
    (mu3GridHitSpecs grid) {} edgeVal
  have h := mu3NativeRunExactSpecsVal_formulaSatisfied
    1128 edgeVal (mu3GridHitSpecs grid) {} edgeVal
    (by rfl) (dimacsFormulaSatisfied_empty edgeVal)
    (dimacsFormulaBounded_empty 1128) (by simp)
    hnonzero hbaseBound hcounts
  refine ⟨out.2, ?_, ?_, h.2.2.2⟩
  · rw [← mu3NativeRunExactSpecsVal_state edgeVal
      (mu3GridHitSpecs grid) {} edgeVal]
    exact h.1
  · rw [← mu3NativeRunExactSpecsVal_state edgeVal
      (mu3GridHitSpecs grid) {} edgeVal]
    exact h.2.1

/-- On old all-TF inputs the parametric specifications are definitionally
the old specifications. -/
theorem mu3GridHitSpecs_ofAllTfShape (shape : Mu3AllTfShape) :
    mu3GridHitSpecs (.ofAllTfShape shape) = mu3NativeHitSpecs shape := by
  rfl

def mu3GridFinalSpecState (grid : Mu3NativeGridSpec) : Mu3NativeCnfState :=
  mu3NativeRunC4PairSpecs mu3NativePairs
    (mu3NativeRunExactSpecs (mu3GridHitSpecs grid) {})

def mu3GridHitSpecVal (grid : Mu3NativeGridSpec)
    (edgeVal : DimacsValuation) : Mu3NativeCnfState × DimacsValuation :=
  mu3NativeRunExactSpecsVal edgeVal (mu3GridHitSpecs grid) {} edgeVal

def mu3GridFinalSpecVal (grid : Mu3NativeGridSpec)
    (edgeVal : DimacsValuation) : Mu3NativeCnfState × DimacsValuation :=
  let hit := mu3GridHitSpecVal grid edgeVal
  mu3NativeRunC4PairSpecsVal edgeVal mu3NativePairs hit.1 hit.2

set_option maxHeartbeats 0 in
/-- Shape-free semantic capstone.  Exact row/column counts and the static
base-edge C4 bound construct a satisfying valuation for the complete
parametric specification state. -/
theorem mu3GridFinalSpecState_formulaSatisfiable
    (grid : Mu3NativeGridSpec) (edgeVal : DimacsValuation)
    (hhitNonzero : ∀ spec ∈ mu3GridHitSpecs grid,
      ∀ lit ∈ spec.1, lit ≠ 0)
    (hhitBound : ∀ spec ∈ mu3GridHitSpecs grid,
      ∀ lit ∈ spec.1, lit.natAbs ≤ 1128)
    (hhitCounts : ∀ spec ∈ mu3GridHitSpecs grid,
      seqPrefixTrue (mu3NativeVarsRow edgeVal spec.1) spec.1.size = spec.2)
    (hbaseC4 : Mu3NativeBaseC4 edgeVal) :
    ∃ val, dimacsFormulaSatisfied val
      (mu3GridFinalSpecState grid).clauses := by
  let hit := mu3GridHitSpecVal grid edgeVal
  have hhit := mu3NativeRunExactSpecsVal_formulaSatisfied
    1128 edgeVal (mu3GridHitSpecs grid) {} edgeVal
    (by rfl) (dimacsFormulaSatisfied_empty edgeVal)
    (dimacsFormulaBounded_empty 1128) (by simp)
    hhitNonzero hhitBound hhitCounts
  have hc4 : Mu3NativeC4FoldConditions 1128 edgeVal
      mu3NativePairs hit.1 hit.2 := by
    apply mu3NativeC4FoldConditions_of_base edgeVal mu3NativePairs
      hit.1 hit.2 hhit.2.2.1 hhit.1 hhit.2.1 hhit.2.2.2
    · intro pair hpair
      exact hpair
    · exact hbaseC4
  have hfinal := mu3NativeRunC4PairSpecsVal_formulaSatisfied
    1128 edgeVal mu3NativePairs hit.1 hit.2 hhit.2.2.1
      hhit.1 hhit.2.1 hhit.2.2.2 hc4
  refine ⟨(mu3GridFinalSpecVal grid edgeVal).2, ?_⟩
  rw [show mu3GridFinalSpecState grid =
      (mu3GridFinalSpecVal grid edgeVal).1 by
        rw [mu3GridFinalSpecVal, mu3GridFinalSpecState,
          mu3NativeRunC4PairSpecsVal_state]
        apply congrArg (mu3NativeRunC4PairSpecs mu3NativePairs)
        exact (mu3NativeRunExactSpecsVal_state edgeVal
          (mu3GridHitSpecs grid) {} edgeVal).symm]
  exact hfinal.1

theorem mu3GridFinalSpecState_ofAllTfShape (shape : Mu3AllTfShape) :
    mu3GridFinalSpecState (.ofAllTfShape shape) =
      mu3NativeFinalSpecState shape := by
  rfl

end Erdos85

#print axioms Erdos85.mu3GridHitSpecs_formulaSatisfiable
#print axioms Erdos85.mu3GridHitSpecs_ofAllTfShape
#print axioms Erdos85.mu3GridFinalSpecState_formulaSatisfiable
#print axioms Erdos85.mu3GridFinalSpecState_ofAllTfShape
