import Proofs.Erdos85OrderFortyNineSevenHighCanonicalCensus
import Proofs.Erdos85OrderFortyNineBooleanTerminal

/-!
# Canonical seven-high profile masks

This is the Lean counterpart of `generate_h7_canonical_cnfs.py`'s vertex
layout: seven highs, triple supports, uncovered pair supports, `deg_T(w)+2`
singleton supports at every high point, and finally empty supports.
-/

namespace Erdos85
namespace OrderFortyNineSevenHighCensus

def tripleMask (triple : Triple) : Nat :=
  triple.foldl (fun mask point => mask + 2 ^ point) 0

def allPairs : List (Nat × Nat) :=
  (List.range 7).flatMap fun a =>
    (List.range 7).filterMap fun b =>
      if a < b then some (a, b) else none

def containsPair (triple : Triple) (pair : Nat × Nat) : Bool :=
  triple.contains pair.1 && triple.contains pair.2

def pairMasks (system : System) : List Nat :=
  allPairs.filterMap fun pair =>
    if system.any fun triple => containsPair triple pair then none
    else some (2 ^ pair.1 + 2 ^ pair.2)

def singletonMasks (system : System) : List Nat :=
  (List.range 7).flatMap fun point =>
    List.replicate
      (system.countP fun triple => triple.contains point) (2 ^ point) ++
    List.replicate 2 (2 ^ point)

def profileMaskList (system : System) : List Nat :=
  let core := List.replicate 7 0 ++ system.map tripleMask ++
    pairMasks system ++ singletonMasks system
  core ++ List.replicate (49 - core.length) 0

def profileMasks (system : System) : Array Nat :=
  (profileMaskList system).toArray

def representativeMasks (blocks index : Nat) : Array Nat :=
  profileMasks ((reps blocks).getD index [])

theorem allPairs_length : allPairs.length = 21 := by native_decide

/-- All fourteen representatives generate exactly 49 support masks. -/
theorem representativeMasks_sizes :
    (List.range 8).all (fun blocks =>
      (List.range (reps blocks).length).all fun index =>
        (representativeMasks blocks index).size == 49) = true := by
  native_decide

/-- The first seven mask entries are zero, so the canonical first seven
vertices are pairwise nonadjacent high vertices. -/
theorem representativeMasks_high_zero
    (blocks index : Nat) :
    ∀ a : Fin 7, orderFortyNineSupportMask
      (representativeMasks blocks index) ⟨a.val, by omega⟩ = 0 := by
  intro a
  fin_cases a <;>
    simp [representativeMasks, profileMasks, profileMaskList,
      orderFortyNineSupportMask]

/-- The canonical representative count agrees with the generated CNF
manifest: fourteen instances in total. -/
theorem total_representative_count :
    ((List.range 8).map fun blocks => (reps blocks).length).sum = 14 := by
  native_decide

end OrderFortyNineSevenHighCensus
end Erdos85
