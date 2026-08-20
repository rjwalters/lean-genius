import Proofs.Erdos85MuNegFiveCanonicalOwnerCnf

/-! Command-line DIMACS emitter for the h504 and h512 owner formulas. -/

namespace Erdos85.MuNegFiveCanonicalOwnerCnfEmit

def clauseLine (clause : DimacsClause) : String :=
  String.intercalate " " (clause.map toString) ++ " 0"

def maxVar (clauses : Array DimacsClause) : Nat :=
  clauses.foldl (fun top clause ↦ clause.foldl (fun top lit ↦
    max top lit.natAbs) top) 0

def emit (path : System.FilePath) (clauses : Array DimacsClause) : IO Unit := do
  let handle ← IO.FS.Handle.mk path IO.FS.Mode.write
  handle.putStr s!"p cnf {maxVar clauses} {clauses.size}\n"
  for clause in clauses do
    handle.putStr (clauseLine clause ++ "\n")

def run (args : List String) : IO UInt32 := do
  match args with
  | [endpoint, phase, path] =>
      let sigma := phase == "1"
      let clauses ← match endpoint with
        | "504" => pure (muNegFiveZeroFourOwnerDimacsClauses sigma)
        | "512" => pure (muNegFiveOneTwoOwnerDimacsClauses sigma)
        | _ =>
            IO.eprintln "endpoint must be 504 or 512"
            return 2
      emit path clauses
      return 0
  | _ =>
      IO.eprintln "usage: <504|512> <0|1> <output.cnf>"
      return 2

end Erdos85.MuNegFiveCanonicalOwnerCnfEmit

def main (args : List String) : IO UInt32 :=
  Erdos85.MuNegFiveCanonicalOwnerCnfEmit.run args
