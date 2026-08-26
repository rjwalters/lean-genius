import Proofs.Erdos85CnfCubeCover
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnf

/-!
# Empty-sector cubes of the compact canonical H7/T0 CNF

The external certificate campaign partitions the canonical instance by the
isomorphism type of the graph induced on its seven empty-support vertices.
This file pins the 43 reviewed representative masks and defines the exact
21-unit CNF consumed by every LRAT certificate.
-/

namespace Erdos85

open Std Sat

/-- Representative masks in the external cuber's stable order.  The four
lists correspond to empty-sector edge counts `6,7,8,9`. -/
def sevenHighT0CanonicalEmptyRepresentativeMasks (edgeCount : Nat) : List Nat :=
  match edgeCount with
  | 6 => [8519, 65863, 1048903, 98375, 294983, 1081415, 786503,
      17159, 139527, 270599, 532743, 786695, 1310983, 1835015,
      360515, 622659, 1085571, 331907, 594051]
  | 7 => [139591, 196935, 328007, 590151, 1114439, 360519, 622663,
      819271, 1343559, 1835079, 541447, 401671, 794887, 1581319,
      1642627]
  | 8 => [663879, 459079, 1245511, 1376583, 1638727, 1867847, 925959]
  | 9 => [1712455, 1507655]
  | _ => []

def sevenHighT0CanonicalEmptyRepresentativeMask
    (edgeCount typeIndex : Nat) : Nat :=
  (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount)[typeIndex]?.getD 0

/-- The single ordered 43-mask inventory used by orbit-cover consumers. -/
def sevenHighT0CanonicalEmptyAllRepresentativeMasks : List Nat :=
  (List.range 4).flatMap fun offset =>
    sevenHighT0CanonicalEmptyRepresentativeMasks (offset + 6)

/-- Edge predicate of a 21-bit empty-sector mask in lexicographic E-pair
order. -/
def sevenHighT0CanonicalEmptyMaskEdge (mask edgeIndex : Nat) : Bool :=
  mask.testBit edgeIndex

/-- The 21 E--E literals, in the same lexicographic pair order as the Python
cuber and the canonical CNF's low-edge numbering. -/
def sevenHighT0CanonicalEmptyMaskUnits (mask : Nat) : Array (Literal Nat) :=
  (sevenHighT0CanonicalLabelPairs.zipIdx.map fun indexedPair =>
    let pair := indexedPair.1
    let index := indexedPair.2
    (sevenHighT0CanonicalLowEdgeId (7 + pair.1) (7 + pair.2),
      sevenHighT0CanonicalEmptyMaskEdge mask index)).toArray

def orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf
    (edgeCount typeIndex : Nat) : CNF Nat :=
  cnfWithUnits orderFortyNineSevenHighT0CanonicalSatCnf
    (sevenHighT0CanonicalEmptyMaskUnits
      (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex))

/-- Certificate-facing proposition for one stable `(F,type)` cube. -/
def SevenHighT0CanonicalEmptyCubeChecked
    (edgeCount typeIndex : Nat) : Prop :=
  (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf
    edgeCount typeIndex).Unsat

/-- A complete checked provider has one proof for every one of the 43 stable
representatives; bounds make missing or surplus type indices explicit. -/
def SevenHighT0CanonicalEmptyCubeCheckedProvider : Prop :=
  ∀ edgeCount, 6 ≤ edgeCount → edgeCount ≤ 9 →
    ∀ typeIndex,
      typeIndex <
        (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount).length →
      SevenHighT0CanonicalEmptyCubeChecked edgeCount typeIndex

set_option maxHeartbeats 0 in
theorem sevenHighT0CanonicalEmptyRepresentativeCounts :
    (sevenHighT0CanonicalEmptyRepresentativeMasks 6).length = 19 ∧
    (sevenHighT0CanonicalEmptyRepresentativeMasks 7).length = 15 ∧
    (sevenHighT0CanonicalEmptyRepresentativeMasks 8).length = 7 ∧
    (sevenHighT0CanonicalEmptyRepresentativeMasks 9).length = 2 := by
  native_decide

set_option maxHeartbeats 0 in
theorem sevenHighT0CanonicalEmptyAllRepresentativeMasks_length :
    sevenHighT0CanonicalEmptyAllRepresentativeMasks.length = 43 := by
  native_decide

set_option maxHeartbeats 0 in
theorem sevenHighT0CanonicalEmptyMaskUnits_size (mask : Nat) :
    (sevenHighT0CanonicalEmptyMaskUnits mask).size = 21 := by
  have hpairs : sevenHighT0CanonicalLabelPairs.length = 21 := by
    native_decide
  simpa [sevenHighT0CanonicalEmptyMaskUnits] using hpairs

set_option maxHeartbeats 0 in
theorem sevenHighT0CanonicalEmptyMaskUnits_f6_type0 :
    sevenHighT0CanonicalEmptyMaskUnits
      (sevenHighT0CanonicalEmptyRepresentativeMask 6 0) =
      #[(1, true), (2, true), (3, true), (4, false), (5, false),
        (6, false), (42, true), (43, false), (44, true), (45, false),
        (46, false), (82, false), (83, false), (84, true), (85, false),
        (121, false), (122, false), (123, false), (159, false),
        (160, false), (196, false)] := by
  native_decide

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyRepresentativeCounts
#print axioms Erdos85.sevenHighT0CanonicalEmptyMaskUnits_f6_type0
