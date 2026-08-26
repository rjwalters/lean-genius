import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticStructure
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfC4Witness

/-! # The executable empty-sector mask of canonical H7 semantics

This file turns the induced graph on the seven empty-support vertices into
the exact 21-bit mask consumed by the checked orbit cover.  The bit order is
the canonical CNF's lexicographic list of label pairs.
-/

namespace Erdos85

open SimpleGraph

def sevenHighT0CanonicalBoolsToNat : List Bool → Nat
  | [] => 0
  | bit :: bits => Nat.bit bit (sevenHighT0CanonicalBoolsToNat bits)

@[simp] theorem sevenHighT0CanonicalBoolsToNat_testBit
    (bits : List Bool) (index : Nat) (hindex : index < bits.length) :
    (sevenHighT0CanonicalBoolsToNat bits).testBit index =
      bits[index]'hindex := by
  induction bits generalizing index with
  | nil => simp at hindex
  | cons bit bits ih =>
      cases index with
      | zero => simp [sevenHighT0CanonicalBoolsToNat]
      | succ index =>
          simp only [sevenHighT0CanonicalBoolsToNat,
            Nat.testBit_bit_succ, List.length_cons,
            Nat.succ_lt_succ_iff] at hindex ⊢
          exact ih index hindex

theorem sevenHighT0CanonicalBoolsToNat_lt_pow_length (bits : List Bool) :
    sevenHighT0CanonicalBoolsToNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [sevenHighT0CanonicalBoolsToNat]
  | cons bit bits ih =>
      cases bit <;>
        simp only [sevenHighT0CanonicalBoolsToNat, Nat.bit_false,
          Nat.bit_true, List.length_cons, pow_succ] <;> omega

def sevenHighT0CanonicalEmptySemanticBits
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    List Bool :=
  sevenHighT0CanonicalLabelPairs.map fun pair =>
    decide (H.Adj
      (Sum.inr (Sum.inl (Fin.ofNat 7 pair.1)))
      (Sum.inr (Sum.inl (Fin.ofNat 7 pair.2))))

def sevenHighT0CanonicalEmptySemanticMask
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] : Nat :=
  sevenHighT0CanonicalBoolsToNat
    (sevenHighT0CanonicalEmptySemanticBits H)

theorem sevenHighT0CanonicalEmptySemanticBits_length
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    (sevenHighT0CanonicalEmptySemanticBits H).length = 21 := by
  change sevenHighT0CanonicalLabelPairs.length = 21
  decide

theorem sevenHighT0CanonicalEmptySemanticMask_lt
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    sevenHighT0CanonicalEmptySemanticMask H < 2 ^ 21 := by
  rw [sevenHighT0CanonicalEmptySemanticMask,
    ← sevenHighT0CanonicalEmptySemanticBits_length H]
  exact sevenHighT0CanonicalBoolsToNat_lt_pow_length _

theorem sevenHighT0CanonicalEmptySemanticMask_testBit
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (index : Fin 21) :
    (sevenHighT0CanonicalEmptySemanticMask H).testBit index.1 =
      decide (H.Adj
        (Sum.inr (Sum.inl
          (Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).1)))
        (Sum.inr (Sum.inl
          (Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).2)))) := by
  have hpairs : sevenHighT0CanonicalLabelPairs.length = 21 := by decide
  have hindex : index.1 < sevenHighT0CanonicalLabelPairs.length := by
    rw [hpairs]
    exact index.2
  have hpair : sevenHighT0CanonicalLabelPairs[index.1] =
      sevenHighT0CanonicalPairNat index := by
    have hlookup := sevenHighT0CanonicalLabelPairs_lookup_pairNat index
    rw [List.getElem?_eq_getElem hindex] at hlookup
    exact Option.some.inj hlookup
  rw [sevenHighT0CanonicalEmptySemanticMask,
    sevenHighT0CanonicalBoolsToNat_testBit]
  · unfold sevenHighT0CanonicalEmptySemanticBits
    rw [List.getElem_map, hpair]
  · rw [sevenHighT0CanonicalEmptySemanticBits_length]
    exact index.2

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMask_testBit
