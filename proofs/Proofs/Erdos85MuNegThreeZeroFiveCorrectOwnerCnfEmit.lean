import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerCnf

/-!
# Exact DIMACS emitter for the honest 88-owner h305 CNF

Run with `lake env lean --run
Proofs/Erdos85MuNegThreeZeroFiveCorrectOwnerCnfEmit.lean
<tf|tri> <tf|tri> <0|1> <output.cnf>`.
-/

namespace Erdos85.MuNegThreeZeroFiveCorrectOwnerCnfEmit

def clauseLine (clause : DimacsClause) : String :=
  String.intercalate " " (clause.map toString) ++ " 0"

def maxVar (clauses : Array DimacsClause) : Nat :=
  clauses.foldl (fun top clause ↦ clause.foldl (fun top lit ↦
    max top lit.natAbs) top) 0

def emit (path : System.FilePath) (clauses : Array DimacsClause) : IO Unit := do
  let handle ← IO.FS.Handle.mk path IO.FS.Mode.write
  handle.putStr s!"p cnf {maxVar clauses} {clauses.size}\n"
  let mut chunk := ""
  for i in [0:clauses.size] do
    chunk := chunk ++ clauseLine clauses[i]! ++ "\n"
    if i % 4096 = 4095 then
      handle.putStr chunk
      chunk := ""
  if !chunk.isEmpty then
    handle.putStr chunk

def parseMode (arg : String) : Option Bool :=
  if arg = "tf" then some false else if arg = "tri" then some true else none

def parsePhase (arg : String) : Option Bool :=
  if arg = "0" then some false else if arg = "1" then some true else none

def run (args : List String) : IO UInt32 := do
  match args with
  | [uMode, vMode, phase, path] =>
      let some uTri := parseMode uMode | do
        IO.eprintln "bad u mode (expected tf or tri)"
        return 2
      let some vTri := parseMode vMode | do
        IO.eprintln "bad v mode (expected tf or tri)"
        return 2
      let some sigma := parsePhase phase | do
        IO.eprintln "bad phase (expected 0 or 1)"
        return 2
      emit path (muNegThreeZeroFiveCorrectOwnerDimacsClauses uTri vTri sigma)
      return 0
  | _ => do
      IO.eprintln "usage: h305-correct-owner-cnf <tf|tri> <tf|tri> <0|1> <output.cnf>"
      return 2

end Erdos85.MuNegThreeZeroFiveCorrectOwnerCnfEmit

def main (args : List String) : IO UInt32 :=
  Erdos85.MuNegThreeZeroFiveCorrectOwnerCnfEmit.run args
