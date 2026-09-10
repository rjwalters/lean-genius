import Proofs.Erdos85OrderFortyNineThreeHighTripleSupportedCandidateSearch
import Proofs.Erdos85EncodedC4CachedRows
open Erdos85
set_option maxRecDepth 100000

def diagnosticP : ThreeBlockFirstRowParameters :=
  (fun _ => ⟨34, by decide⟩, Equiv.swap 1 2)
def diagnosticQ : ThreeHighSecondaryTuple := (2, fun _ => none, true)


def profileU := threeHighFullUnionAdj (threeBlockFirstRowEmbed diagnosticP)
def profileR := threeHighSecondaryTupleAdj diagnosticQ

def profileGate (name : String) (gate : ThreeHighCross → Bool) : IO Unit := do
  let start ← IO.monoMsNow
  let mut count := 0
  for _ in [:100] do
    for S in threeHighCrossRowList profileU 0 do
      let cross := threeHighCrossOfRows (Function.update (fun _ => ∅) 0 S)
      if gate cross then count := count + 1
  let finish ← IO.monoMsNow
  IO.println s!"{name}: accepted={count}, elapsed_ms={finish-start}"
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println s!"row0_options={(threeHighCrossRowList profileU 0).length}; repetitions=100"
  (← IO.getStdout).flush
  profileGate "C4_cached" (fun cross => encodedC4FreeCachedRows (threeHighEmptyAdj profileU profileR cross))
  profileGate "capacity" (threeHighCrossCapacity profileR)
  profileGate "canFill" (fun cross => threeHighCrossCanFill profileR cross 1)
