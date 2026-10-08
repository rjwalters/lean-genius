import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCnf

/- Streaming DIMACS print of the exact Lean term
`orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i` (the 21-unit cube of the compact
canonical H7/T0 CNF), in Lean clause order, Std.Sat variable `v` written as DIMACS `v + 1`
(the inverse of `dimacsClauseToSatClause`; same convention as
`h35_probe_20261007/EmitCanonical.lean`).  The header's variable count is the Lean value
`sevenHighT0CanonicalFinalState.top`.

    lake env lean --run EmitCube.lean F0 i0 F1 i1 ...   -- one CNF per (F, i), concatenated
-/

open Erdos85 Std Sat

def litStr (l : Nat × Bool) : String :=
  (if l.2 then "" else "-") ++ toString (l.1 + 1)

def emit (cnf : CNF Nat) (nvars : Nat) : IO Unit := do
  let cs := cnf.clauses
  IO.print s!"p cnf {nvars} {cs.size}\n"
  let mut chunk := ""
  for i in [0:cs.size] do
    let c := cs[i]!
    chunk := chunk ++ String.intercalate " " (c.map litStr) ++ " 0\n"
    if i % 4096 = 4095 then
      IO.print chunk
      chunk := ""
  if !chunk.isEmpty then IO.print chunk

partial def loop : List String → IO UInt32
  | f :: i :: rest => do
      emit (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf f.toNat! i.toNat!)
        sevenHighT0CanonicalFinalState.top
      loop rest
  | [] => pure 0
  | _ => do IO.eprintln "usage: F i [F i ...]"; pure 2

def main (args : List String) : IO UInt32 := loop args
