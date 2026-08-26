import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnf

/-! Streaming DIMACS emitter for byte-identity checks of the canonical CNF. -/

namespace Erdos85.SevenHighT0CanonicalCnfEmit

def clauseLine (clause : DimacsClause) : String :=
  String.intercalate " " (clause.map toString) ++ " 0"

def emit : IO Unit := do
  let st := sevenHighT0CanonicalFinalState
  IO.print s!"p cnf {st.top} {st.clauses.size}\n"
  let mut chunk := ""
  for i in [0:st.clauses.size] do
    chunk := chunk ++ clauseLine st.clauses[i]! ++ "\n"
    if i % 4096 = 4095 then
      IO.print chunk
      chunk := ""
  if !chunk.isEmpty then IO.print chunk

end Erdos85.SevenHighT0CanonicalCnfEmit

def main (_args : List String) : IO UInt32 := do
  Erdos85.SevenHighT0CanonicalCnfEmit.emit
  pure 0
