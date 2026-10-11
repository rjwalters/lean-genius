import Proofs.Erdos85ThreeHighFirstColumnSearch
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable

/-! Diagnostic first-column inventory only. No complete branch search and no
rejection theorem is evaluated here. Run on the cloud builder. -/

open Erdos85 Lean

namespace FirstColumnInventory

def fullU (a b : Fin 15) (c : Fin 120) : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode a b c))

def deficientU (a b : Fin 15) (c : Fin 120) (d : Fin 5) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj
    (threeBlockDeficientFirstRowEmbed (threeBlockDeficientCompactCode a b c d))

def secondary (r : Fin 21) : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative r)

def inventory (name : String)
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool) : IO Unit := do
  let candidates := threeHighStaticPrunedColumnList U R 0
  let gate := threeHighFactoredColumnGate U R
  let branches := candidates.map fun S =>
    let mask := (List.finRange 15).foldl
      (fun n i => if i ∈ S then n + 2 ^ i.val else n) (0 : Nat)
    let first := Function.update (fun _ : Fin 8 => (∅ : Finset (Fin 15))) 0 S
    (mask, gate 1 first)
  IO.println (Json.mkObj [
    ("case", toJson name),
    ("static_count", toJson candidates.length),
    ("prefix_survivors", toJson (branches.filter (fun branch => branch.2)).length),
    ("columns_mask_and_prefix_pass", toJson branches)]).compress

#eval inventory "FullU1R15" (fullU 6 6 15) (secondary 15)
#eval inventory "FullU3R3" (fullU 6 9 5) (secondary 3)
#eval inventory "FullU54R20" (fullU 9 12 90) (secondary 20)
#eval inventory "DeficientU26R2" (deficientU 6 9 11 1) (secondary 2)
#eval inventory "DeficientU369R11" (deficientU 9 12 92 2) (secondary 11)

end FirstColumnInventory
