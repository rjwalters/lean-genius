import Proofs.Erdos85OrderFortyNineThreeHighTripleSupportedCandidateSearch
import Proofs.Erdos85ThreeHighBlockDeficit
open Erdos85
set_option maxRecDepth 100000

def diagnosticP : ThreeBlockFirstRowParameters :=
  (fun _ => ⟨34, by decide⟩, Equiv.swap 1 2)
def diagnosticQ : ThreeHighSecondaryTuple := (2, fun _ => none, true)


def profileU := threeHighFullUnionAdj (threeBlockFirstRowEmbed diagnosticP)
def profileR := threeHighSecondaryTupleAdj diagnosticQ


def bump (r : IO.Ref (Array Nat)) (i : Nat) : IO Unit :=
  r.modify (fun a => a.modify i (· + 1))

def traceDFS (stats depths : IO.Ref (Array Nat)) :
    Nat → Nat → (Fin 15 → Finset (Fin 8)) → IO Unit
  | 0, _, rows => do
      bump stats 4
      let cross := threeHighCrossOfRows rows
      if encodedDegreeProfile (threeHighEmptyAdj profileU profileR cross)
          (fun i => if i = 23 then 6 else 4) then bump stats 5
  | fuel+1, k, rows => do
      if hk : k < 15 then
        for S in threeHighRootPrunedRowList profileU ⟨k,hk⟩ do
          if (← stats.get)[0]! >= 5000 then return
          bump stats 0
          bump depths k
          let next := Function.update rows ⟨k,hk⟩ S
          let cross := threeHighCrossOfRows next
          if !threeHighCrossCapacity profileR cross then bump stats 1
          else if !threeHighCrossBlockCanFill profileR cross (k+1) threeHighUBlock then bump stats 2
          else if !(threeHighUnionBlockCap profileU && threeHighCrossBlockCap cross) then bump stats 6
          else if !encodedC4FreeCachedRows (threeHighEmptyAdj profileU profileR cross) then bump stats 3
          else traceDFS stats depths fuel (k+1) next
          let a ← stats.get
          if a[0]! % 1000 == 0 then
            IO.println s!"progress stats={a}"
            (← IO.getStdout).flush

def main : IO Unit := do
  let stats ← IO.mkRef (Array.replicate 7 0)
  let depths ← IO.mkRef (Array.replicate 15 0)
  IO.println "starting root/factored/block-deficit bounded outer DFS; prefix_limit=5000; terminal_family_search=disabled"
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  traceDFS stats depths 15 0 (fun _ => ∅)
  let finish ← IO.monoMsNow
  IO.println s!"stats[attempt,capacity_fail,deficit_fail,c4_fail,leaf,degree_valid_leaf,external_fail]={← stats.get}"
  IO.println s!"depth_attempts={← depths.get}; elapsed_ms={finish-start}"
  (← IO.getStdout).flush
