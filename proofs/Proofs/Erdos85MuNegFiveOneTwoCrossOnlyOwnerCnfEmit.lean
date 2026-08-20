import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyOwnerCnf

namespace Erdos85.MuNegFiveOneTwoCrossOnlyOwnerCnfEmit

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
  | [phase, path] =>
      let sigma := phase == "1"
      emit path (muNegFiveOneTwoCrossOnlyOwnerDimacsClauses sigma)
      return 0
  | _ =>
      IO.eprintln "usage: <0|1> <output.cnf>"
      return 2

end Erdos85.MuNegFiveOneTwoCrossOnlyOwnerCnfEmit

def main (args : List String) : IO UInt32 :=
  Erdos85.MuNegFiveOneTwoCrossOnlyOwnerCnfEmit.run args
