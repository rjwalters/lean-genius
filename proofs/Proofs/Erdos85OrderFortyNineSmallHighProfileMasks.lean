import Proofs.Erdos85OrderFortyNineBooleanTerminal

/-!
# Canonical profile masks for the three- and five-high strata

The mask order matches the durable survivor generators: high vertices first,
then triple supports, uncovered pair supports, singleton supports grouped by
high point, and finally empty supports.
-/

namespace Erdos85
namespace OrderFortyNineSmallHighCensus

abbrev Triple := List Nat
abbrev System := List Triple

def tripleMask (triple : Triple) : Nat :=
  triple.foldl (fun mask point => mask + 2 ^ point) 0

def allPairs (h : Nat) : List (Nat × Nat) :=
  (List.range h).flatMap fun a =>
    (List.range h).filterMap fun b =>
      if a < b then some (a, b) else none

def containsPair (triple : Triple) (pair : Nat × Nat) : Bool :=
  triple.contains pair.1 && triple.contains pair.2

def pairMasks (h : Nat) (system : System) : List Nat :=
  (allPairs h).filterMap fun pair =>
    if system.any fun triple => containsPair triple pair then none
    else some (2 ^ pair.1 + 2 ^ pair.2)

/-- A point has `9-h` singleton supports in the empty triple system.  Every
triple through it consumes two pair supports and contributes one triple
support, so one additional singleton restores degree eight. -/
def singletonMasks (h : Nat) (system : System) : List Nat :=
  (List.range h).flatMap fun point =>
    List.replicate
      (9 - h + system.countP fun triple => triple.contains point)
      (2 ^ point)

def profileMaskList (h : Nat) (system : System) : List Nat :=
  let core := List.replicate h 0 ++ system.map tripleMask ++
    pairMasks h system ++ singletonMasks h system
  core ++ List.replicate (49 - core.length) 0

def profileMasks (h : Nat) (system : System) : Array Nat :=
  (profileMaskList h system).toArray

def threeHighSystems : List System :=
  [[], [[0, 1, 2]]]

def fiveHighSystems : List System :=
  [[], [[0, 1, 2]], [[0, 1, 2], [0, 3, 4]]]

def threeHighRepresentativeMasks (index : Nat) : Array Nat :=
  profileMasks 3 (threeHighSystems.getD index [])

def fiveHighRepresentativeMasks (index : Nat) : Array Nat :=
  profileMasks 5 (fiveHighSystems.getD index [])

theorem threeHighRepresentativeMasks_sizes :
    (List.range 2).all fun index =>
      (threeHighRepresentativeMasks index).size == 49 := by
  native_decide

theorem fiveHighRepresentativeMasks_sizes :
    (List.range 3).all fun index =>
      (fiveHighRepresentativeMasks index).size == 49 := by
  native_decide

theorem threeHighRepresentativeMasks_high_zero (index : Nat) :
    ∀ a : Fin 3, orderFortyNineSupportMask
      (threeHighRepresentativeMasks index) ⟨a.val, by omega⟩ = 0 := by
  intro a
  fin_cases a <;>
    simp [threeHighRepresentativeMasks, profileMasks, profileMaskList,
      orderFortyNineSupportMask]

theorem fiveHighRepresentativeMasks_high_zero (index : Nat) :
    ∀ a : Fin 5, orderFortyNineSupportMask
      (fiveHighRepresentativeMasks index) ⟨a.val, by omega⟩ = 0 := by
  intro a
  fin_cases a <;>
    simp [fiveHighRepresentativeMasks, profileMasks, profileMaskList,
      orderFortyNineSupportMask]

/-- The constructed arrays realize the classified support-cardinality
censuses `(n0,n1,n2,n3)` for h=3. -/
theorem threeHighRepresentativeMask_census :
    (List.range 2).map (fun index =>
      (List.range 49).map (fun vertex =>
        (List.range 3).countP fun w =>
          (threeHighRepresentativeMasks index)[vertex]!.testBit w)) =
      [
        List.replicate 3 0 ++ List.replicate 3 2 ++
          List.replicate 18 1 ++ List.replicate 25 0,
        List.replicate 3 0 ++ [3] ++ List.replicate 21 1 ++
          List.replicate 24 0
      ] := by
  native_decide

/-- The analogous h=5 censuses are `(14,20,10,0)`, `(13,23,7,1)`, and
`(12,26,4,2)` in the generator's ordered layout. -/
theorem fiveHighRepresentativeMask_census :
    (List.range 3).map (fun index =>
      (List.range 49).map (fun vertex =>
        (List.range 5).countP fun w =>
          (fiveHighRepresentativeMasks index)[vertex]!.testBit w)) =
      [
        List.replicate 5 0 ++ List.replicate 10 2 ++
          List.replicate 20 1 ++ List.replicate 14 0,
        List.replicate 5 0 ++ [3] ++ List.replicate 7 2 ++
          List.replicate 23 1 ++ List.replicate 13 0,
        List.replicate 5 0 ++ [3, 3] ++ List.replicate 4 2 ++
          List.replicate 26 1 ++ List.replicate 12 0
      ] := by
  native_decide

end OrderFortyNineSmallHighCensus
end Erdos85
