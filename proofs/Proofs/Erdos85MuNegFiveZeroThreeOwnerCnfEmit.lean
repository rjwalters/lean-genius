import Proofs.Erdos85MuNegFiveZeroThreeOwnerCnf

/-!
# Exact DIMACS emitter for the h503 owner CNF

Run with `lake env lean --run Proofs/Erdos85MuNegFiveZeroThreeOwnerCnfEmit.lean
<false|true>`.  The phase argument is the relative sign phase `sigma` used by
the signed `3+2` cross-owner degree constraints.
-/

namespace Erdos85

namespace MuNegFiveZeroThreeOwnerCnfEmit

def clauseLine (clause : DimacsClause) : String :=
  String.intercalate " " (clause.map toString) ++ " 0"

def topVariable (clauses : Array DimacsClause) : Nat := Id.run do
  let mut top := 0
  for clause in clauses do
    for lit in clause do
      top := max top lit.natAbs
  return top

/-- Stream the formula instead of constructing one large output string. -/
def emitDimacs (clauses : Array DimacsClause) : IO Unit := do
  IO.print s!"p cnf {topVariable clauses} {clauses.size}\n"
  let mut chunk := ""
  for i in [0:clauses.size] do
    chunk := chunk ++ clauseLine clauses[i]! ++ "\n"
    if i % 4096 = 4095 then
      IO.print chunk
      chunk := ""
  if !chunk.isEmpty then
    IO.print chunk

def run (args : List String) : IO UInt32 := do
  match args with
  | [phase] =>
      let some sigma :=
          if phase = "false" || phase = "0" then some false
          else if phase = "true" || phase = "1" then some true
          else none | do
        IO.eprintln "bad phase (expected false/true or 0/1)"
        return 2
      emitDimacs (muNegFiveZeroThreeDimacsClauses sigma)
      return 0
  | _ => do
      IO.eprintln "usage: h503-owner-cnf <false|true>"
      return 2

end MuNegFiveZeroThreeOwnerCnfEmit

end Erdos85

def main (args : List String) : IO UInt32 :=
  Erdos85.MuNegFiveZeroThreeOwnerCnfEmit.run args
