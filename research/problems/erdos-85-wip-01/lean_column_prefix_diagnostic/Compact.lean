import Proofs.Erdos85ThreeHighStaticCapacityColumnDFS
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
open Erdos85
set_option maxRecDepth 100000
def U := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))
def R := threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)
structure Stats where
  nodes : Nat := 0
  capacity : Nat := 0
  externalCap : Nat := 0
  c4 : Nat := 0
  leaves : Nat := 0
  deriving Repr
partial def visit (domains : Array (List (Finset (Fin 15)))) (degrees : Array Nat)
    (stats : IO.Ref Stats) (limit k : Nat) (columns : Fin 8 → Finset (Fin 15)) : IO Bool := do
  if k == 8 then
    let cross := threeHighCrossOfColumns columns
    if !(encodedDegreeProfile (threeHighEmptyAdj U R cross) (fun i => if i = 23 then 6 else 4)) then
      throw (IO.userError "bad leaf degree")
    stats.modify fun s => {s with leaves := s.leaves+1}
    return true
  if h : k < 8 then
    for column in domains[k]! do
      if (← stats.get).nodes >= limit then return false
      stats.modify fun s => {s with nodes := s.nodes+1}
      let next := Function.update columns ⟨k,h⟩ column
      let cross := threeHighCrossOfColumns next
      if !(threeHighColumnRowCapacityFor (fun i => degrees[i.val]!) cross (k+1)) then
        stats.modify fun s => {s with capacity := s.capacity+1}
      else if !(encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow) then
        stats.modify fun s => {s with externalCap := s.externalCap+1}
      else if !(encodedC4FreeCachedRows (threeHighEmptyAdj U R cross)) then
        stats.modify fun s => {s with c4 := s.c4+1}
      else
        if !(← visit domains degrees stats limit (k+1) next) then return false
    return true
  else return true
def main : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn "entered setup"
  out.flush
  let start ← IO.monoMsNow
  let domains := Array.ofFn (threeHighStaticPrunedColumnList U R)
  out.putStrLn s!"domains={domains.map List.length}"
  out.flush
  let ready ← IO.monoMsNow
  let degrees := Array.ofFn (fun i : Fin 15 => encodedRowDegree (U i))
  let stats ← IO.mkRef ({} : Stats)
  let exhausted ← visit domains degrees stats 5000 0 (fun _ => ∅)
  out.putStrLn s!"exhausted={exhausted} stats={repr (← stats.get)}"
  out.flush
  let stop ← IO.monoMsNow
  out.putStrLn s!"setup_ms={ready-start} traversal_ms={stop-ready}"
