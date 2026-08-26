import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptySemanticOrbitCover
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfSatisfaction

/-! # Sound residual-stabilizer normalization for canonical H7 cubes -/

namespace Erdos85

open SimpleGraph

/-- A total numeric code for the 861 semantic low-edge bits, in the exact
DIMACS edge-variable order.  Minimizing this code is a deterministic lex
normal form; no auxiliary SAT variable enters the definition. -/
def sevenHighT0CanonicalSemanticEdgeCode
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] : Nat :=
  (List.range 861).foldl (fun code offset =>
    2 * code + if sevenHighT0CanonicalEdgeVal H (offset + 1) then 1 else 0) 0

/-- The subgroup predicate used by one pinned empty mask.  Its orientation
matches the pullback convention in `sevenHighT0CanonicalRelabel`. -/
def sevenHighT0CanonicalEmptyMaskStabilizes
    (mask : Nat) (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∀ left right : Fin 7,
    sevenHighT0CanonicalEmptySemanticMaskAdj mask
        (σ.symm left).1 (σ.symm right).1 =
      sevenHighT0CanonicalEmptySemanticMaskAdj mask left.1 right.1

instance (mask : Nat) (σ : Equiv.Perm (Fin 7)) :
    Decidable (sevenHighT0CanonicalEmptyMaskStabilizes mask σ) := by
  unfold sevenHighT0CanonicalEmptyMaskStabilizes
  infer_instance

theorem sevenHighT0CanonicalEmptyMaskStabilizes_refl (mask : Nat) :
    sevenHighT0CanonicalEmptyMaskStabilizes mask (Equiv.refl (Fin 7)) := by
  intro left right
  rfl

/-- A stabilizer relabel preserves the pinned semantic empty mask exactly. -/
theorem sevenHighT0CanonicalEmptySemanticMask_relabel_eq_of_stabilizes
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (mask : Nat) (hmask : sevenHighT0CanonicalEmptySemanticMask H = mask)
    (σ : Equiv.Perm (Fin 7))
    (hstabilizes : sevenHighT0CanonicalEmptyMaskStabilizes mask σ) :
    sevenHighT0CanonicalEmptySemanticMask
        (sevenHighT0CanonicalRelabel σ H) = mask := by
  apply sevenHighT0CanonicalEmptyMask_eq_of_adj
    (sevenHighT0CanonicalEmptySemanticMask_lt _)
    (hmask ▸ sevenHighT0CanonicalEmptySemanticMask_lt H)
  intro left right
  rw [sevenHighT0CanonicalEmptySemanticMaskAdj_relabel, hmask]
  exact hstabilizes left right

/-- Every completion pinned to `mask` has a least semantic-edge code among
all relabelings from the *actual stabilizer of that mask*.  This is the formal
orbit-coverage fact required before adding residual lex-leader clauses. -/
theorem SevenHighT0CanonicalCompletionSemantics.exists_stabilizerLex_relabel
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (mask : Nat) (hmask : sevenHighT0CanonicalEmptySemanticMask H = mask) :
    ∃ σ : Equiv.Perm (Fin 7),
      sevenHighT0CanonicalEmptyMaskStabilizes mask σ ∧
      SevenHighT0CanonicalCompletionSemantics
        (sevenHighT0CanonicalRelabel σ H) ∧
      sevenHighT0CanonicalEmptySemanticMask
          (sevenHighT0CanonicalRelabel σ H) = mask ∧
      ∀ τ : Equiv.Perm (Fin 7),
        sevenHighT0CanonicalEmptyMaskStabilizes mask τ →
        sevenHighT0CanonicalSemanticEdgeCode
            (sevenHighT0CanonicalRelabel σ H) ≤
          sevenHighT0CanonicalSemanticEdgeCode
            (sevenHighT0CanonicalRelabel τ H) := by
  let Stabilizer := {σ : Equiv.Perm (Fin 7) //
    sevenHighT0CanonicalEmptyMaskStabilizes mask σ}
  let candidates : Finset Stabilizer := Finset.univ
  have hnonempty : candidates.Nonempty := by
    refine ⟨⟨Equiv.refl (Fin 7),
      sevenHighT0CanonicalEmptyMaskStabilizes_refl mask⟩, Finset.mem_univ _⟩
  obtain ⟨chosen, hchosen, hleast⟩ := candidates.exists_min_image
    (fun σ => sevenHighT0CanonicalSemanticEdgeCode
      (sevenHighT0CanonicalRelabel σ.1 H)) hnonempty
  refine ⟨chosen.1, chosen.2, semantics.relabel chosen.1,
    sevenHighT0CanonicalEmptySemanticMask_relabel_eq_of_stabilizes
      H mask hmask chosen.1 chosen.2, ?_⟩
  intro τ hτ
  exact hleast ⟨τ, hτ⟩ (Finset.mem_univ _)

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMask_relabel_eq_of_stabilizes
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.exists_stabilizerLex_relabel
