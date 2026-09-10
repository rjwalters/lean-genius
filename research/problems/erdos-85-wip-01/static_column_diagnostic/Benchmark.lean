import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighStaticColumnPruning
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
open Erdos85
set_option maxRecDepth 100000

def runStaticColumnBenchmark : IO Unit := do
  let U := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))
  let R := threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)
  let t0 ← IO.monoMsNow
  let a := (List.finRange 8).map fun j => (threeHighCompactColumnList R j).length
  IO.println s!"compact sizes={a}"
  let t1 ← IO.monoMsNow
  let b := (List.finRange 8).map fun j => (threeHighStaticPrunedColumnList U R j).length
  IO.println s!"static sizes={b}"
  let t2 ← IO.monoMsNow
  IO.println s!"compact_ms={t1-t0}, static_ms={t2-t1}"
#eval runStaticColumnBenchmark
