import Proofs.Erdos85OrderFortyNineCanonicalCnf
import Proofs.Erdos85OrderFortyNineSmallHighProfileMasks

/- Emit the exact `CNF Nat` consumed by
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks`:
`orderFortyNineGeneratedCanonicalSatCnf 3 (threeHighRepresentativeMasks i)`, i ∈ {0,1}
`orderFortyNineGeneratedCanonicalSatCnf 5 (fiveHighRepresentativeMasks i)`,  i ∈ {0,1,2}
as DIMACS, in Lean clause order, mapping Std.Sat variable v to DIMACS id v+1
(exact inverse of `dimacsClauseToSatClause`, same convention as h3-lean-exact/EmitScout.lean). -/

open Erdos85 Std Sat Erdos85.OrderFortyNineSmallHighCensus

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

def main (args : List String) : IO UInt32 := do
  match args with
  | ["h3", i] =>
      emit (orderFortyNineGeneratedCanonicalSatCnf 3 (threeHighRepresentativeMasks i.toNat!))
        (orderFortyNineDegreeBlocks 3).top; pure 0
  | ["h5", i] =>
      emit (orderFortyNineGeneratedCanonicalSatCnf 5 (fiveHighRepresentativeMasks i.toNat!))
        (orderFortyNineDegreeBlocks 5).top; pure 0
  | _ => IO.eprintln "usage: h3 <0|1> | h5 <0|1|2>"; pure 2
