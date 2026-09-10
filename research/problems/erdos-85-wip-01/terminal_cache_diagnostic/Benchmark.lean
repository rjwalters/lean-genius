import Proofs.Erdos85ThreeHighCachedSupportClosure
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates
import Proofs.Erdos85ThreeHighExternalBlockFactorization
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
namespace ColumnCanary
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def U := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))
def R := threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)
def rows : Fin 15 → BitVec 8 := ![2,4,16,64,160,32,128,2,8,80,16,4,32,64,136]
def cross : ThreeHighCross := fun i j => (rows i).getLsbD j.val

end ColumnCanary
def main : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn "entered evaluation"
  out.flush
  let start ← IO.monoMsNow
  let result := Erdos85.threeHighCachedSeparatedJointSearch
    (Erdos85.threeHighEmptyAdj ColumnCanary.U ColumnCanary.R ColumnCanary.cross)
  out.putStrLn s!"terminal={result}"
  out.flush
  let stop ← IO.monoMsNow
  out.putStrLn s!"elapsed_ms={stop-start}"
  out.flush
