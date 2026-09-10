import Proofs.Erdos85ThreeHighSeparatedGate
open Erdos85

def testResidual : Finset (Fin 24) := Finset.univ.filter (fun i => i.val < 18)
def disjointTriples : List (Finset (Fin 24)) :=
  (List.finRange 6).map fun k =>
    {⟨3*k.val, by omega⟩, ⟨3*k.val+1, by omega⟩, ⟨3*k.val+2, by omega⟩}
def overlappingTriples : List (Finset (Fin 24)) :=
  ((List.finRange 24).filter (fun x => decide (x.val < 18 ∧ x ≠ 7 ∧ x ≠ 8))).map
    (fun x => {x,7,8})

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem accepts_disjoint : threeHighSeparatedGate disjointTriples testResidual = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem rejects_despite_coverage :
    threeHighSeparatedGate overlappingTriples testResidual = false ∧
    (∀ x ∈ testResidual, ∃ S ∈ overlappingTriples, x ∈ S) := by decide
#print axioms accepts_disjoint
#print axioms rejects_despite_coverage
