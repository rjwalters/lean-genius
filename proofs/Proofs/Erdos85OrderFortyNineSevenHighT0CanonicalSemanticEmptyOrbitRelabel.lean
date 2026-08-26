import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticEmptyMask

/-! # Relabeling action on the semantic empty-sector mask

The orbit cover uses raw 21-bit masks, while canonical semantics relabel the
whole H/E/S/P graph.  This file identifies those actions at the adjacency
level, independently of the expensive finite orbit enumeration.
-/

namespace Erdos85

open SimpleGraph

private theorem sevenHighT0CanonicalEmptySemanticMaskAdj_pairNat
    (mask : Nat) (index : Fin 21) :
    sevenHighT0CanonicalEmptySemanticMaskAdj mask
        (Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).1).1
        (Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).2).1 =
      mask.testBit index.1 := by
  let left := Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).1
  let right := Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).2
  have hvalid := sevenHighT0CanonicalPairNat_valid index
  have hleft : left.1 = (sevenHighT0CanonicalPairNat index).1 := by
    exact Nat.mod_eq_of_lt hvalid.1
  have hright : right.1 = (sevenHighT0CanonicalPairNat index).2 := by
    exact Nat.mod_eq_of_lt hvalid.2.1
  have hlt : left.1 < right.1 := by simpa [hleft, hright] using hvalid.2.2
  have hne : left.1 ≠ right.1 := ne_of_lt hlt
  have hidx : sevenHighT0CanonicalLabelPairs.idxOf
      ((sevenHighT0CanonicalPairNat index).1,
        (sevenHighT0CanonicalPairNat index).2) = index.1 := by
    fin_cases index <;> decide
  change sevenHighT0CanonicalEmptySemanticMaskAdj
      mask left.1 right.1 = _
  rw [sevenHighT0CanonicalEmptySemanticMaskAdj]
  have hbne : (left.1 != right.1) = true := by simp [hne]
  rw [hbne, Bool.true_and, min_eq_left (le_of_lt hlt),
    max_eq_right (le_of_lt hlt), hleft, hright, hidx]

/-- A 21-bit mask is determined by the executable adjacency predicate on
the seven empty labels. -/
theorem sevenHighT0CanonicalEmptyMask_eq_of_adj
    {leftMask rightMask : Nat}
    (hleft : leftMask < 2 ^ 21) (hright : rightMask < 2 ^ 21)
    (hadj : ∀ left right : Fin 7,
      sevenHighT0CanonicalEmptySemanticMaskAdj
          leftMask left.1 right.1 =
        sevenHighT0CanonicalEmptySemanticMaskAdj
          rightMask left.1 right.1) :
    leftMask = rightMask := by
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases hindex : index < 21
  · let i : Fin 21 := ⟨index, hindex⟩
    have h := hadj
      (Fin.ofNat 7 (sevenHighT0CanonicalPairNat i).1)
      (Fin.ofNat 7 (sevenHighT0CanonicalPairNat i).2)
    rw [sevenHighT0CanonicalEmptySemanticMaskAdj_pairNat,
      sevenHighT0CanonicalEmptySemanticMaskAdj_pairNat] at h
    exact h
  · have hpow : 2 ^ 21 ≤ 2 ^ index := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (hleft.trans_le hpow),
      Nat.testBit_eq_false_of_lt (hright.trans_le hpow)]

theorem sevenHighT0CanonicalEmptySemanticMaskAdj_relabel
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (σ : Equiv.Perm (Fin 7)) (left right : Fin 7) :
    sevenHighT0CanonicalEmptySemanticMaskAdj
        (sevenHighT0CanonicalEmptySemanticMask
          (sevenHighT0CanonicalRelabel σ H)) left.1 right.1 =
      sevenHighT0CanonicalEmptySemanticMaskAdj
        (sevenHighT0CanonicalEmptySemanticMask H)
          (σ.symm left).1 (σ.symm right).1 := by
  rw [sevenHighT0CanonicalEmptySemanticMaskAdj_eq,
    sevenHighT0CanonicalEmptySemanticMaskAdj_eq]
  rfl

theorem sevenHighT0CanonicalEmptySemanticMaskAdj_relabel_symm
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (σ : Equiv.Perm (Fin 7)) (left right : Fin 7) :
    sevenHighT0CanonicalEmptySemanticMaskAdj
        (sevenHighT0CanonicalEmptySemanticMask
          (sevenHighT0CanonicalRelabel σ.symm H)) left.1 right.1 =
      sevenHighT0CanonicalEmptySemanticMaskAdj
        (sevenHighT0CanonicalEmptySemanticMask H)
          (σ left).1 (σ right).1 := by
  simpa using sevenHighT0CanonicalEmptySemanticMaskAdj_relabel
    H σ.symm left right

/-- Extensional consumer for an externally represented relabeled mask. -/
theorem sevenHighT0CanonicalEmptySemanticMask_relabel_eq_of_adj
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (σ : Equiv.Perm (Fin 7)) (targetMask : Nat)
    (htarget : targetMask < 2 ^ 21)
    (hadj : ∀ left right : Fin 7,
      sevenHighT0CanonicalEmptySemanticMaskAdj
          targetMask left.1 right.1 =
        sevenHighT0CanonicalEmptySemanticMaskAdj
          (sevenHighT0CanonicalEmptySemanticMask H)
          (σ.symm left).1 (σ.symm right).1) :
    sevenHighT0CanonicalEmptySemanticMask
        (sevenHighT0CanonicalRelabel σ H) = targetMask := by
  apply sevenHighT0CanonicalEmptyMask_eq_of_adj
    (sevenHighT0CanonicalEmptySemanticMask_lt _) htarget
  intro left right
  rw [sevenHighT0CanonicalEmptySemanticMaskAdj_relabel]
  exact (hadj left right).symm

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMaskAdj_relabel
#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMask_relabel_eq_of_adj
