import Proofs.Erdos85ThreeHighCompactColumnDFS
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
open Erdos85
set_option maxRecDepth 100000

def runColumnDomainBenchmark : IO Unit := do
  let R := threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)
  let t0 ← IO.monoMsNow
  let a := (List.finRange 8).map fun j => (threeHighCrossColumnList R j).length
  IO.println s!"baseline sizes={a}"
  let t1 ← IO.monoMsNow
  let b := (List.finRange 8).map fun j => (threeHighCompactColumnList R j).length
  IO.println s!"compact sizes={b}"
  let t2 ← IO.monoMsNow
  IO.println s!"baseline_ms={t1-t0}, compact_ms={t2-t1}"
#eval runColumnDomainBenchmark
