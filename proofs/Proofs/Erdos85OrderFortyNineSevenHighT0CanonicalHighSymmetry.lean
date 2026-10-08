import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalRelabeling
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticEmptyOrbitRelabel

/-! # High-side symmetry of the canonical H7/T0 completion problem

The diagonal relabeling of `...CanonicalRelabeling` moves the seven
empty-support vertices together with the high labels, so inside a pinned
empty-mask cube only the (tiny) mask stabilizer survives.  But the empty
vertices have no high neighbours: the high labels can be permuted, and the
two singleton copies of each label swapped, while every empty vertex stays
fixed.  This action of `S₇ ⋉ (ℤ/2)⁷` (order 645,120) preserves the completion
semantics and the semantic empty mask *exactly*, hence acts inside every
pinned cube.  It is the symmetry consumed by the `hsb` clauses of
`research/problems/erdos-85-wip-01/h7_structural_pilot_20261008`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- High-side action on the 42 low indices: empties fixed, singleton
`(w, c) ↦ (σ w, flip w c)`, pair `{a, b} ↦ {σ a, σ b}`. -/
def sevenHighT0LowIndexHighPerm (σ : Equiv.Perm (Fin 7))
    (flip : Fin 7 → Equiv.Perm (Fin 2)) :
    SevenHighT0LowIndex ≃ SevenHighT0LowIndex :=
  Equiv.sumCongr (Equiv.refl (Fin 7))
    (Equiv.sumCongr (Equiv.prodShear σ flip)
      (sevenHighT0PairIndexPerm σ))

/-- High-side action on the complete canonical 49-index. -/
def sevenHighT0CanonicalIndexHighPerm (σ : Equiv.Perm (Fin 7))
    (flip : Fin 7 → Equiv.Perm (Fin 2)) :
    SevenHighT0CanonicalIndex ≃ SevenHighT0CanonicalIndex :=
  Equiv.sumCongr σ (sevenHighT0LowIndexHighPerm σ flip)

/-- Pull a canonical completion graph along a high-side symmetry. -/
def sevenHighT0CanonicalHighRelabel (σ : Equiv.Perm (Fin 7))
    (flip : Fin 7 → Equiv.Perm (Fin 2))
    (H : SimpleGraph SevenHighT0CanonicalIndex) :
    SimpleGraph SevenHighT0CanonicalIndex :=
  H.comap (sevenHighT0CanonicalIndexHighPerm σ flip).symm

instance sevenHighT0CanonicalHighRelabel_adj_decidable
    (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2))
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    DecidableRel (sevenHighT0CanonicalHighRelabel σ flip H).Adj := by
  intro i j
  change Decidable (H.Adj _ _)
  infer_instance

/-- Canonical completion semantics are invariant under the high-side
action. -/
theorem SevenHighT0CanonicalCompletionSemantics.highRelabel
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H)
    (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2)) :
    SevenHighT0CanonicalCompletionSemantics
      (sevenHighT0CanonicalHighRelabel σ flip H) := by
  refine
    { c4Free := ?_
      high_high := ?_
      high_empty := ?_
      high_singleton := ?_
      high_pair := ?_
      low_degree := ?_ }
  · intro hc4
    exact hH.c4Free ((containsC4_iff_of_iso
      (SimpleGraph.Iso.comap
        (sevenHighT0CanonicalIndexHighPerm σ flip).symm H)).mp hc4)
  · intro w z
    change ¬ H.Adj (Sum.inl (σ.symm w)) (Sum.inl (σ.symm z))
    exact hH.high_high _ _
  · intro w copy
    change ¬ H.Adj (Sum.inl (σ.symm w)) (Sum.inr (Sum.inl copy))
    exact hH.high_empty _ _
  · intro w q
    change H.Adj (Sum.inl (σ.symm w))
      (Sum.inr (Sum.inr (Sum.inl
        (σ.symm q.1, (flip (σ.symm q.1)).symm q.2)))) ↔ w = q.1
    rw [hH.high_singleton]
    exact σ.symm.injective.eq_iff
  · intro w key
    change H.Adj (Sum.inl (σ.symm w))
      (Sum.inr (Sum.inr (Sum.inr
        (sevenHighT0PairIndexPerm σ.symm key)))) ↔ _
    rw [hH.high_pair]
    simpa using
      sevenHighT0PairIndexPerm_endpoint_iff σ.symm (σ.symm w) key
  · intro i
    have hdegree :
        ((H.comap Sum.inr).comap
            (sevenHighT0LowIndexHighPerm σ flip).symm).degree i =
          (H.comap Sum.inr).degree
            ((sevenHighT0LowIndexHighPerm σ flip).symm i) :=
      (SimpleGraph.Iso.comap
        (sevenHighT0LowIndexHighPerm σ flip).symm
          (H.comap Sum.inr)).degree_eq i |>.symm
    change ((H.comap Sum.inr).comap
      (sevenHighT0LowIndexHighPerm σ flip).symm).degree i +
        sevenHighT0LowIndexSupportCard i = 7
    rw [hdegree]
    have hsupport :
        sevenHighT0LowIndexSupportCard
            ((sevenHighT0LowIndexHighPerm σ flip).symm i) =
          sevenHighT0LowIndexSupportCard i := by
      rcases i with i | i
      · rfl
      · rcases i with i | i <;> rfl
    rw [← hsupport]
    exact hH.low_degree ((sevenHighT0LowIndexHighPerm σ flip).symm i)

/-- The high-side action fixes the semantic empty mask exactly: it acts
inside every pinned empty-mask cube. -/
theorem sevenHighT0CanonicalEmptySemanticMask_highRelabel
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2)) :
    sevenHighT0CanonicalEmptySemanticMask
        (sevenHighT0CanonicalHighRelabel σ flip H) =
      sevenHighT0CanonicalEmptySemanticMask H := by
  apply sevenHighT0CanonicalEmptyMask_eq_of_adj
    (sevenHighT0CanonicalEmptySemanticMask_lt _)
    (sevenHighT0CanonicalEmptySemanticMask_lt H)
  intro left right
  rw [sevenHighT0CanonicalEmptySemanticMaskAdj_eq,
    sevenHighT0CanonicalEmptySemanticMaskAdj_eq]
  rfl

end

end Erdos85

#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.highRelabel
#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMask_highRelabel
