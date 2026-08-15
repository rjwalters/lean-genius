import Proofs.Erdos85OrderFortyNineTableVerification

/-!
# Executable canonical census for the seven-high stratum

The size-three high supports form a linear triple system on seven points.
After sending one block to `012`, the executable raw census is exhaustive.
This file kernel-checks that every raw system is permutation-equivalent to one
of fourteen representatives, distributed `1,1,2,3,3,2,1,1` by block count.
-/

namespace Erdos85
namespace OrderFortyNineSevenHighCensus

set_option maxRecDepth 100000

abbrev Triple := List Nat
abbrev System := List Triple

def allTriples : List Triple :=
  (List.range 7).flatMap fun a =>
    (List.range 7).flatMap fun b =>
      (List.range 7).filterMap fun c =>
        if a < b ∧ b < c then some [a, b, c] else none

def linearWith (triple : Triple) (system : System) : Bool :=
  system.all fun prior =>
    Nat.ble (triple.countP fun point => prior.contains point) 1

def pointDegreesAtMostThree (system : System) : Bool :=
  (List.range 7).all fun point =>
    Nat.ble (system.countP fun triple => triple.contains point) 3

def extendLinear : Nat → List Triple → System → List System
  | 0, _, system =>
      if pointDegreesAtMostThree system then [system.reverse] else []
  | _ + 1, [], _ => []
  | need + 1, triple :: remaining, system =>
      extendLinear (need + 1) remaining system ++
        if linearWith triple system then
          extendLinear need remaining (triple :: system)
        else []

def rawSystems : Nat → List System
  | 0 => [[]]
  | blocks + 1 =>
      extendLinear blocks allTriples.tail [[0, 1, 2]]

def reps : Nat → List System
  | 0 => [[]]
  | 1 => [[ [0, 1, 2] ]]
  | 2 => [
      [[0, 1, 2], [0, 3, 4]],
      [[0, 1, 2], [3, 4, 5]]]
  | 3 => [
      [[0, 1, 2], [0, 3, 4], [0, 5, 6]],
      [[0, 1, 2], [0, 3, 4], [1, 3, 5]],
      [[0, 1, 2], [0, 3, 4], [1, 5, 6]]]
  | 4 => [
      [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5]],
      [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]],
      [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 6]]]
  | 5 => [
      [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6]],
      [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [2, 4, 6]]]
  | 6 => [[
      [0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6]]]
  | 7 => [[
      [0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6],
      [2, 3, 6], [2, 4, 5]]]
  | _ => []

def applyPermutation (permutation : List Nat) (system : System) : System :=
  system.map fun triple => triple.map fun point => permutation.getD point 0

def coveredByReps (blocks : Nat) (system : System) : Bool :=
  (List.range 7).permutations.any fun permutation =>
    (reps blocks).any fun representative =>
      OrderFortyNineWitnessTable.systemSetEqB
        (applyPermutation permutation system) representative

theorem allTriples_length : allTriples.length = 35 := by native_decide

theorem rawSystems_lengths :
    (List.range 8).map (fun blocks => (rawSystems blocks).length) =
      [1, 1, 22, 135, 264, 150, 36, 6] := by
  native_decide

theorem reps_lengths :
    (List.range 8).map (fun blocks => (reps blocks).length) =
      [1, 1, 2, 3, 3, 2, 1, 1] := by
  native_decide

/-- Every prefix-normalized seven-point linear triple system with at most
three blocks through any point is isomorphic to a stored representative. -/
theorem rawSystems_covered :
    (List.range 8).all fun blocks =>
      (rawSystems blocks).all (coveredByReps blocks) = true := by
  native_decide

end OrderFortyNineSevenHighCensus
end Erdos85
