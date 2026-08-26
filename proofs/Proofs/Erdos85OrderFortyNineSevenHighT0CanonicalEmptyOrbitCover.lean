import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCnf
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalRelabeling

/-! # Checked S7-orbit cover for the canonical empty graph

The external cuber quotients admissible graphs on the seven empty-support
vertices by all permutations of the seven high labels.  Here the same finite
claim is recomputed inside Lean: the admissible 21-bit masks are exactly the
union of the full orbits of the 43 pinned representatives.
-/

namespace Erdos85

structure SevenHighT0CanonicalEmptyRepresentative where
  edgeCount : Nat
  typeIndex : Nat
  mask : Nat
deriving DecidableEq, Repr

def sevenHighT0CanonicalEmptyRepresentatives :
    List SevenHighT0CanonicalEmptyRepresentative :=
  (List.range 4).flatMap fun offset =>
    let edgeCount := offset + 6
    (List.range
      (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount).length).map
        fun typeIndex =>
          { edgeCount, typeIndex,
            mask := sevenHighT0CanonicalEmptyRepresentativeMask
              edgeCount typeIndex }

def sevenHighT0CanonicalEmptyEdgeCount (mask : Nat) : Nat :=
  (List.range 21).countP mask.testBit

def sevenHighT0CanonicalEmptyAdj (mask left right : Nat) : Bool :=
  left != right && mask.testBit
    (sevenHighT0CanonicalLabelPairs.idxOf
      (min left right, max left right))

def sevenHighT0CanonicalEmptyDegree (mask vertex : Nat) : Nat :=
  (List.range 7).countP fun other =>
    sevenHighT0CanonicalEmptyAdj mask vertex other

def sevenHighT0CanonicalEmptyCommonCount (mask left right : Nat) : Nat :=
  (List.range 7).countP fun witness =>
    sevenHighT0CanonicalEmptyAdj mask left witness &&
      sevenHighT0CanonicalEmptyAdj mask right witness

/-- The exact filters used by the reviewed Python cuber: maximum degree three
and at most one common neighbor for each distinct vertex pair. -/
def sevenHighT0CanonicalEmptyPassesGraphFilters (mask : Nat) : Bool :=
  ((List.range 7).all fun vertex =>
      decide (sevenHighT0CanonicalEmptyDegree mask vertex ≤ 3)) &&
  (sevenHighT0CanonicalLabelPairs.all fun pair =>
      decide (sevenHighT0CanonicalEmptyCommonCount mask pair.1 pair.2 ≤ 1))

def sevenHighT0CanonicalEmptyAdmissible (mask : Nat) : Bool :=
  decide (mask < 2 ^ 21) &&
  decide (6 ≤ sevenHighT0CanonicalEmptyEdgeCount mask) &&
  decide (sevenHighT0CanonicalEmptyEdgeCount mask ≤ 10) &&
  sevenHighT0CanonicalEmptyPassesGraphFilters mask

def sevenHighT0CanonicalEmptyAdmissibleMasks : List Nat :=
  (List.range (2 ^ 21)).filter sevenHighT0CanonicalEmptyAdmissible

/-- The 5,040 permutations in the executable representation used by the
external cuber.  Membership proves that a row is a permutation of
`[0,1,...,6]`; conversion to an `Equiv.Perm (Fin 7)` is kept separate from
the finite orbit computation. -/
def sevenHighT0CanonicalPermutationRows : List (List Nat) :=
  (List.range 7).permutations

/-- Transport a 21-bit empty-graph mask along a high-label permutation. -/
def sevenHighT0CanonicalEmptyPermutedMask
    (permutation : List Nat) (mask : Nat) : Nat :=
  (sevenHighT0CanonicalLabelPairs.zipIdx.map fun indexedPair =>
    let pair := indexedPair.1
    let index := indexedPair.2
    if mask.testBit index then
      let left := permutation.getD pair.1 0
      let right := permutation.getD pair.2 0
      2 ^ (sevenHighT0CanonicalLabelPairs.idxOf
        (min left right, max left right))
    else 0).sum

def sevenHighT0CanonicalEmptyRepresentativeOrbitMasks : List Nat :=
  sevenHighT0CanonicalEmptyRepresentatives.flatMap fun representative =>
    sevenHighT0CanonicalPermutationRows.map fun permutation =>
      sevenHighT0CanonicalEmptyPermutedMask permutation representative.mask

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The 43 pinned representatives cover every labeled mask passing the exact
edge-count, maximum-degree, and common-neighbor filters. -/
theorem sevenHighT0CanonicalEmptyRepresentative_orbit_cover :
    sevenHighT0CanonicalEmptyAdmissibleMasks.toFinset =
      sevenHighT0CanonicalEmptyRepresentativeOrbitMasks.toFinset := by
  native_decide

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyRepresentative_orbit_cover
