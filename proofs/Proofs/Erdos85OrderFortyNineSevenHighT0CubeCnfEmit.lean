import Proofs.Erdos85OrderFortyNineSevenHighT0CubeCnf

/-! Streaming DIMACS emitter for byte-identity checks of the t=0 cubes. -/

namespace Erdos85.SevenHighT0CubeCnfEmit

def clauseLine (clause : DimacsClause) : String :=
  String.intercalate " " (clause.map toString) ++ " 0"

def emit (cube : Nat) : IO Unit := do
  let st := sevenHighT0CubeFinalState cube
  IO.print s!"p cnf {st.top} {st.clauses.size}\n"
  let mut chunk := ""
  for i in [0:st.clauses.size] do
    chunk := chunk ++ clauseLine st.clauses[i]! ++ "\n"
    if i % 4096 = 4095 then
      IO.print chunk
      chunk := ""
  if !chunk.isEmpty then
    IO.print chunk

def run (args : List String) : IO UInt32 := do
  match args with
  | [cubeText] =>
      match cubeText.toNat? with
      | some cube =>
          if cube < 7 then
            emit cube
            pure 0
          else
            IO.eprintln "cube must be in 0..6"
            pure 2
      | none =>
          IO.eprintln "cube must be a natural number"
          pure 2
  | _ =>
      IO.eprintln "usage: <program> CUBE"
      pure 2

end Erdos85.SevenHighT0CubeCnfEmit

def main (args : List String) : IO UInt32 :=
  Erdos85.SevenHighT0CubeCnfEmit.run args
