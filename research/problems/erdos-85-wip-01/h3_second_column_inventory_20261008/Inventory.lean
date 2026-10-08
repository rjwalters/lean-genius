import Proofs.Erdos85ThreeHighSecondColumnSearch
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable

/-! Diagnostic two-column inventory for the two forced-first-column cases.
No complete branch search or concrete rejection is evaluated. Cloud only. -/

open Erdos85 Lean

namespace SecondColumnInventory

def fullU (a b : Fin 15) (c : Fin 120) : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode a b c))

def deficientU (a b : Fin 15) (c : Fin 120) (d : Fin 5) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj
    (threeBlockDeficientFirstRowEmbed (threeBlockDeficientCompactCode a b c d))

def secondary (r : Fin 21) : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative r)

def inventory (name : String)
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool) : IO Unit := do
  let uRows := Vector.ofFn (fun i => Vector.ofFn (U i))
  let rRows := Vector.ofFn (fun i => Vector.ofFn (R i))
  let cachedU := fun i j => (uRows.get i).get j
  let cachedR := fun i j => (rRows.get i).get j
  let firstCandidates := threeHighStaticPrunedColumnList cachedU cachedR 0
  let secondCandidates := threeHighStaticPrunedColumnList cachedU cachedR 1
  let gate := threeHighFactoredColumnGate cachedU cachedR
  let maskOf := fun S : Finset (Fin 15) => (List.finRange 15).foldl
    (fun n i => if i ∈ S then n + 2 ^ i.val else n) (0 : Nat)
  let branches := firstCandidates.flatMap fun S =>
    let first := Function.update (fun _ : Fin 8 => (∅ : Finset (Fin 15))) 0 S
    secondCandidates.map fun T =>
      let second := Function.update first 1 T
      Json.mkObj [
        ("first_mask", toJson (maskOf S)),
        ("second_mask", toJson (maskOf T)),
        ("first_gate", toJson (gate 1 first)),
        ("second_gate", toJson (gate 2 second))]
  IO.println (Json.mkObj [
    ("case", toJson name),
    ("first_masks", toJson (firstCandidates.map maskOf)),
    ("second_masks", toJson (secondCandidates.map maskOf)),
    ("static_pair_count", toJson branches.length),
    ("branches", toJson branches)]).compress

#eval inventory "FullU3R3" (fullU 6 9 5) (secondary 3)
#eval inventory "DeficientU26R2" (deficientU 6 9 11 1) (secondary 2)

end SecondColumnInventory
