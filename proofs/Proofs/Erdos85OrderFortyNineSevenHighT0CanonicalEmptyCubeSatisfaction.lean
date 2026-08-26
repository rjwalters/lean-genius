import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticEmptyMask
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCnf

/-! # Adding a representative empty mask to a semantic CNF model -/

namespace Erdos85

open SimpleGraph Std Sat

theorem sevenHighT0CanonicalEdgeVal_emptyPair
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (index : Fin 21) :
    sevenHighT0CanonicalEdgeVal H
        (sevenHighT0CanonicalLowEdgeId
          (7 + (sevenHighT0CanonicalPairNat index).1)
          (7 + (sevenHighT0CanonicalPairNat index).2)) =
      (sevenHighT0CanonicalEmptySemanticMask H).testBit index.1 := by
  let pair := sevenHighT0CanonicalPairNat index
  have hp := sevenHighT0CanonicalPairNat_valid index
  let a : Fin 49 := ⟨7 + pair.1, by dsimp [pair]; omega⟩
  let b : Fin 49 := ⟨7 + pair.2, by dsimp [pair]; omega⟩
  have hab : a ≠ b := by
    apply Fin.ne_of_val_ne
    dsimp [a, b, pair]
    omega
  rw [show 7 + pair.1 = a.1 by rfl, show 7 + pair.2 = b.1 by rfl,
    sevenHighT0CanonicalEdgeVal_edge H a b
      (by dsimp [a, pair]; omega) (by dsimp [b, pair]; omega) hab]
  rw [sevenHighT0CanonicalEmptySemanticMask_testBit]
  fin_cases index <;>
    simp [pair, a, b, sevenHighT0CanonicalAdjBool,
      sevenHighT0CanonicalIndexOfFin,
      sevenHighT0CanonicalPairNat, Fin.ofNat]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem sevenHighT0CanonicalEmptyMaskUnits_get
    (mask : Nat) (index : Fin 21) :
    (sevenHighT0CanonicalEmptyMaskUnits mask)[index.1] =
      (sevenHighT0CanonicalLowEdgeId
        (7 + (sevenHighT0CanonicalPairNat index).1)
        (7 + (sevenHighT0CanonicalPairNat index).2),
       mask.testBit index.1) := by
  have hpairs : sevenHighT0CanonicalLabelPairs.length = 21 := by decide
  have hindex : index.1 < sevenHighT0CanonicalLabelPairs.length := by
    rw [hpairs]
    exact index.2
  have hpair : sevenHighT0CanonicalLabelPairs[index.1] =
      sevenHighT0CanonicalPairNat index := by
    have hlookup := sevenHighT0CanonicalLabelPairs_lookup_pairNat index
    rw [List.getElem?_eq_getElem hindex] at hlookup
    exact Option.some.inj hlookup
  unfold sevenHighT0CanonicalEmptyMaskUnits
  change (sevenHighT0CanonicalLabelPairs.zipIdx.map fun indexedPair =>
    (sevenHighT0CanonicalLowEdgeId
      (7 + indexedPair.1.1) (7 + indexedPair.1.2),
     sevenHighT0CanonicalEmptyMaskEdge mask indexedPair.2)
    )[index.1] = _
  rw [List.getElem_map, List.getElem_zipIdx, hpair]
  simp [sevenHighT0CanonicalEmptyMaskEdge]

set_option maxRecDepth 100000 in
/-- A semantic model of the compact base CNF also models the 21 unit clauses
pinning its own empty-sector mask. -/
theorem sevenHighT0CanonicalEmptyMask_sat
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (mask : Nat)
    (hbase : orderFortyNineSevenHighT0CanonicalSatCnf.Sat
      (sevenHighT0CanonicalEdgeVal H))
    (hmask : sevenHighT0CanonicalEmptySemanticMask H = mask) :
    (cnfWithUnits orderFortyNineSevenHighT0CanonicalSatCnf
      (sevenHighT0CanonicalEmptyMaskUnits mask)).Sat
        (sevenHighT0CanonicalEdgeVal H) := by
  apply (sat_cnfWithUnits_iff _ _ _).2
  refine ⟨hbase, ?_⟩
  intro index hindex
  have hsize : (sevenHighT0CanonicalEmptyMaskUnits mask).size = 21 := by
    change sevenHighT0CanonicalLabelPairs.length = 21
    decide
  have hi21 : index < 21 := by omega
  let i : Fin 21 := ⟨index, hi21⟩
  rw [show (sevenHighT0CanonicalEmptyMaskUnits mask)[index] =
      (sevenHighT0CanonicalLowEdgeId
        (7 + (sevenHighT0CanonicalPairNat i).1)
        (7 + (sevenHighT0CanonicalPairNat i).2),
       mask.testBit i.1) from
    sevenHighT0CanonicalEmptyMaskUnits_get mask i]
  rw [sevenHighT0CanonicalEdgeVal_emptyPair H i, hmask]
  simp

theorem sevenHighT0CanonicalEmptyRepresentativeCube_sat
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (edgeCount typeIndex : Nat)
    (hbase : orderFortyNineSevenHighT0CanonicalSatCnf.Sat
      (sevenHighT0CanonicalEdgeVal H))
    (hmask : sevenHighT0CanonicalEmptySemanticMask H =
      sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex) :
    (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf
      edgeCount typeIndex).Sat (sevenHighT0CanonicalEdgeVal H) := by
  exact sevenHighT0CanonicalEmptyMask_sat H _ hbase hmask

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEdgeVal_emptyPair
#print axioms Erdos85.sevenHighT0CanonicalEmptyMaskUnits_get
#print axioms Erdos85.sevenHighT0CanonicalEmptyRepresentativeCube_sat
