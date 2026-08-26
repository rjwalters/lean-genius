import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticEmptyMask

/-! # Relabeling action on the semantic empty-sector mask

The orbit cover uses raw 21-bit masks, while canonical semantics relabel the
whole H/E/S/P graph.  This file identifies those actions at the adjacency
level, independently of the expensive finite orbit enumeration.
-/

namespace Erdos85

open SimpleGraph

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

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMaskAdj_relabel
