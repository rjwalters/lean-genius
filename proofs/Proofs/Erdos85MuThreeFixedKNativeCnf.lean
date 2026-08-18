import Proofs.Erdos85MuThreeAllTfNativeCnf

/-!
# A cell-list-parametric native CNF for fixed-K grids

The trusted counter and C4 layers do not depend on the all-TF identity
`K = H`.  They depend only on the ordered list of 48 occupied cells and on
the fixed internal relation `H`, which determines every row/column hit.
This module isolates precisely that boundary.  The old three-shape generator
is recovered by `Mu3NativeGridSpec.ofAllTfShape`.
-/

namespace Erdos85

structure Mu3NativeGridSpec where
  cells : List Nat
  internal : Nat → Nat → Bool

def Mu3NativeGridSpec.ofAllTfShape (shape : Mu3AllTfShape) :
    Mu3NativeGridSpec where
  cells := mu3AllTfCells shape
  internal := mu3AllTfInternal shape

def mu3GridCellIndex (grid : Mu3NativeGridSpec) (cell : Nat) : Nat :=
  grid.cells.idxOf cell

def mu3GridRowVars (grid : Mu3NativeGridSpec) (u x : Nat) : Array Int :=
  (grid.cells.filter fun cell =>
      cell / 8 = x && mu3GridCellIndex grid cell ≠ u).toArray.map
    fun cell => (mu3NativeEdgeId u (mu3GridCellIndex grid cell) : Int)

def mu3GridColumnVars (grid : Mu3NativeGridSpec) (u y : Nat) : Array Int :=
  (grid.cells.filter fun cell =>
      cell % 8 = y && mu3GridCellIndex grid cell ≠ u).toArray.map
    fun cell => (mu3NativeEdgeId u (mu3GridCellIndex grid cell) : Int)

def mu3GridHitBlocks (grid : Mu3NativeGridSpec) : Mu3NativeCnfState :=
  (List.range 48).foldl (fun st u =>
    let cell := grid.cells.getD u 0
    let xu := cell / 8
    let yu := cell % 8
    let st := (List.range 8).foldl (fun st x =>
      mu3NativeEquals (mu3GridRowVars grid u x)
        (if grid.internal x yu then 0 else 1) st) st
    (List.range 8).foldl (fun st y =>
      mu3NativeEquals (mu3GridColumnVars grid u y)
        (if grid.internal xu y then 0 else 1) st) st) {}

def mu3GridFinalState (grid : Mu3NativeGridSpec) : Mu3NativeCnfState :=
  mu3NativePairs.foldl (fun st pair => mu3NativeC4PairStep pair st)
    (mu3GridHitBlocks grid)

def mu3GridNativeSatCnf (grid : Mu3NativeGridSpec) : Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses (mu3GridFinalState grid).clauses

/-- The parametric generator is definitionally compatible with the three
already-checked all-TF generators. -/
theorem mu3GridFinalState_ofAllTfShape (shape : Mu3AllTfShape) :
    mu3GridFinalState (.ofAllTfShape shape) = mu3NativeFinalState shape := by
  rfl

theorem mu3GridNativeSatCnf_ofAllTfShape (shape : Mu3AllTfShape) :
    mu3GridNativeSatCnf (.ofAllTfShape shape) = mu3AllTfNativeSatCnf shape := by
  rfl

end Erdos85

#print axioms Erdos85.mu3GridFinalState_ofAllTfShape
#print axioms Erdos85.mu3GridNativeSatCnf_ofAllTfShape
