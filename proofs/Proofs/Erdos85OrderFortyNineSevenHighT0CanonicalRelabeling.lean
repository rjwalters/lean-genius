import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemantics
import Mathlib.Data.Sym.Sym2.Order

/-! # Simultaneous high-label relabeling of the canonical H7/T0 index

The 43 empty-graph cube representatives are taken modulo permutations of the
seven high labels.  Such a permutation must act simultaneously on the high,
empty-, singleton-, and pair-support vertices.  This file constructs that
action as an actual equivalence of the canonical 49-vertex index.
-/

namespace Erdos85

noncomputable section

private theorem sevenHighT0_not_isDiag_inf_ne_sup
    {z : Sym2 (Fin 7)} (hz : ¬ z.IsDiag) : z.inf ≠ z.sup := by
  induction z using Sym2.ind with
  | _ a b =>
      simp only [Sym2.mk_isDiag_iff] at hz
      simp only [Sym2.inf_mk, Sym2.sup_mk]
      intro hab
      apply hz
      rcases le_total a b with h | h
      · simpa [h] using hab
      · symm
        simpa [h] using hab

/-- Ordered distinct pairs are the same data as off-diagonal symmetric
pairs. -/
def sevenHighT0PairIndexSym2Equiv :
    SevenHighT0PairIndex ≃ {z : Sym2 (Fin 7) // ¬ z.IsDiag} where
  toFun key := ⟨s(key.1.1, key.1.2), by
    simpa using ne_of_lt key.2⟩
  invFun z :=
    ⟨(z.1.inf, z.1.sup),
      lt_of_le_of_ne z.1.inf_le_sup
        (sevenHighT0_not_isDiag_inf_ne_sup z.2)⟩
  left_inv key := by
    apply Subtype.ext
    simp [min_eq_left (le_of_lt key.2), max_eq_right (le_of_lt key.2)]
  right_inv z := by
    apply Subtype.ext
    exact (Sym2.sortEquiv.symm_apply_apply z.1)

/-- Functorial action of an equivalence on symmetric pairs. -/
def sevenHighT0Sym2Perm (σ : Equiv.Perm (Fin 7)) :
    Sym2 (Fin 7) ≃ Sym2 (Fin 7) where
  toFun := Sym2.map σ
  invFun := Sym2.map σ.symm
  left_inv z := by
    induction z using Sym2.ind with
    | _ a b => simp
  right_inv z := by
    induction z using Sym2.ind with
    | _ a b => simp

/-- The symmetric-pair action restricts to off-diagonal pairs. -/
def sevenHighT0OffDiagSym2Perm (σ : Equiv.Perm (Fin 7)) :
    {z : Sym2 (Fin 7) // ¬ z.IsDiag} ≃
      {z : Sym2 (Fin 7) // ¬ z.IsDiag} where
  toFun z := ⟨sevenHighT0Sym2Perm σ z.1, by
    rw [show sevenHighT0Sym2Perm σ z.1 = Sym2.map σ z.1 from rfl,
      Sym2.isDiag_map σ.injective]
    exact z.2⟩
  invFun z := ⟨sevenHighT0Sym2Perm σ.symm z.1, by
    rw [show sevenHighT0Sym2Perm σ.symm z.1 = Sym2.map σ.symm z.1 from rfl,
      Sym2.isDiag_map σ.symm.injective]
    exact z.2⟩
  left_inv z := by
    apply Subtype.ext
    exact (sevenHighT0Sym2Perm σ).left_inv z.1
  right_inv z := by
    apply Subtype.ext
    exact (sevenHighT0Sym2Perm σ).right_inv z.1

/-- Relabel an unordered high-label pair and return it in the canonical
increasing-pair representation. -/
def sevenHighT0PairIndexPerm (σ : Equiv.Perm (Fin 7)) :
    SevenHighT0PairIndex ≃ SevenHighT0PairIndex :=
  sevenHighT0PairIndexSym2Equiv |>.trans
    ((sevenHighT0OffDiagSym2Perm σ).trans
      sevenHighT0PairIndexSym2Equiv.symm)

theorem sevenHighT0PairIndexPerm_sym2
    (σ : Equiv.Perm (Fin 7)) (key : SevenHighT0PairIndex) :
    (sevenHighT0PairIndexSym2Equiv
      (sevenHighT0PairIndexPerm σ key)).1 =
      Sym2.map σ (sevenHighT0PairIndexSym2Equiv key).1 := by
  simp [sevenHighT0PairIndexPerm, sevenHighT0OffDiagSym2Perm,
    sevenHighT0Sym2Perm]

theorem sevenHighT0PairIndexPerm_endpoint_iff
    (σ : Equiv.Perm (Fin 7)) (w : Fin 7)
    (key : SevenHighT0PairIndex) :
    w = (sevenHighT0PairIndexPerm σ key).1.1 ∨
        w = (sevenHighT0PairIndexPerm σ key).1.2 ↔
      σ.symm w = key.1.1 ∨ σ.symm w = key.1.2 := by
  rw [← Sym2.mem_iff, ← Sym2.mem_iff]
  change w ∈
      (sevenHighT0PairIndexSym2Equiv
        (sevenHighT0PairIndexPerm σ key)).1 ↔ _
  rw [sevenHighT0PairIndexPerm_sym2, Sym2.mem_map]
  constructor
  · rintro ⟨a, ha, hσ⟩
    change a ∈ s(key.1.1, key.1.2) at ha
    rw [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · rw [← hσ]
      simp
    · rw [← hσ]
      simp
  · intro hmem
    change σ.symm w ∈ s(key.1.1, key.1.2) at hmem
    rw [Sym2.mem_iff] at hmem
    rcases hmem with h | h
    · refine ⟨key.1.1, ?_, ?_⟩
      · change key.1.1 ∈ s(key.1.1, key.1.2)
        exact Sym2.mem_mk_left _ _
      rw [← h]
      simp
    · refine ⟨key.1.2, ?_, ?_⟩
      · change key.1.2 ∈ s(key.1.1, key.1.2)
        exact Sym2.mem_mk_right _ _
      rw [← h]
      simp

/-- Simultaneous permutation action on all 42 canonical low indices. -/
def sevenHighT0LowIndexPerm (σ : Equiv.Perm (Fin 7)) :
    SevenHighT0LowIndex ≃ SevenHighT0LowIndex :=
  Equiv.sumCongr σ
    (Equiv.sumCongr
      (Equiv.prodCongr σ (Equiv.refl (Fin 2)))
      (sevenHighT0PairIndexPerm σ))

/-- Simultaneous permutation action on the complete canonical 49-index. -/
def sevenHighT0CanonicalIndexPerm (σ : Equiv.Perm (Fin 7)) :
    SevenHighT0CanonicalIndex ≃ SevenHighT0CanonicalIndex :=
  Equiv.sumCongr σ (sevenHighT0LowIndexPerm σ)

@[simp] theorem sevenHighT0LowIndexPerm_supportCard
    (σ : Equiv.Perm (Fin 7)) (i : SevenHighT0LowIndex) :
    sevenHighT0LowIndexSupportCard (sevenHighT0LowIndexPerm σ i) =
      sevenHighT0LowIndexSupportCard i := by
  rcases i with i | i
  · rfl
  · rcases i with i | i <;> rfl

@[simp] theorem sevenHighT0CanonicalIndexPerm_high
    (σ : Equiv.Perm (Fin 7)) (w : Fin 7) :
    sevenHighT0CanonicalIndexPerm σ (Sum.inl w) = Sum.inl (σ w) := rfl

@[simp] theorem sevenHighT0CanonicalIndexPerm_empty
    (σ : Equiv.Perm (Fin 7)) (w : Fin 7) :
    sevenHighT0CanonicalIndexPerm σ (Sum.inr (Sum.inl w)) =
      Sum.inr (Sum.inl (σ w)) := rfl

@[simp] theorem sevenHighT0CanonicalIndexPerm_singleton
    (σ : Equiv.Perm (Fin 7)) (w : Fin 7) (copy : Fin 2) :
    sevenHighT0CanonicalIndexPerm σ
        (Sum.inr (Sum.inr (Sum.inl (w, copy)))) =
      Sum.inr (Sum.inr (Sum.inl (σ w, copy))) := rfl

/-- Pull a canonical completion graph along a simultaneous high-label
permutation. -/
def sevenHighT0CanonicalRelabel
    (σ : Equiv.Perm (Fin 7))
    (H : SimpleGraph SevenHighT0CanonicalIndex) :
    SimpleGraph SevenHighT0CanonicalIndex :=
  H.comap (sevenHighT0CanonicalIndexPerm σ).symm

instance sevenHighT0CanonicalRelabel_adj_decidable
    (σ : Equiv.Perm (Fin 7))
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    DecidableRel (sevenHighT0CanonicalRelabel σ H).Adj := by
  intro i j
  change Decidable (H.Adj _ _)
  infer_instance

/-- Canonical completion semantics are invariant under simultaneous
permutation of all seven high labels. -/
theorem SevenHighT0CanonicalCompletionSemantics.relabel
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H)
    (σ : Equiv.Perm (Fin 7)) :
    SevenHighT0CanonicalCompletionSemantics
      (sevenHighT0CanonicalRelabel σ H) := by
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
        (sevenHighT0CanonicalIndexPerm σ).symm H)).mp hc4)
  · intro w z
    change ¬ H.Adj (Sum.inl (σ.symm w)) (Sum.inl (σ.symm z))
    exact hH.high_high _ _
  · intro w copy
    change ¬ H.Adj (Sum.inl (σ.symm w))
      (Sum.inr (Sum.inl (σ.symm copy)))
    exact hH.high_empty _ _
  · intro w q
    change H.Adj (Sum.inl (σ.symm w))
      (Sum.inr (Sum.inr (Sum.inl (σ.symm q.1, q.2)))) ↔ w = q.1
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
        ((H.comap Sum.inr).comap (sevenHighT0LowIndexPerm σ).symm).degree i =
          (H.comap Sum.inr).degree ((sevenHighT0LowIndexPerm σ).symm i) :=
      (SimpleGraph.Iso.comap
        (sevenHighT0LowIndexPerm σ).symm (H.comap Sum.inr)).degree_eq i |>.symm
    change ((H.comap Sum.inr).comap
      (sevenHighT0LowIndexPerm σ).symm).degree i +
        sevenHighT0LowIndexSupportCard i = 7
    rw [hdegree]
    have hsupport :
        sevenHighT0LowIndexSupportCard
            ((sevenHighT0LowIndexPerm σ).symm i) =
          sevenHighT0LowIndexSupportCard i := by
      rcases i with i | i
      · rfl
      · rcases i with i | i <;> rfl
    rw [← hsupport]
    exact hH.low_degree ((sevenHighT0LowIndexPerm σ).symm i)

end

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalIndexPerm
#print axioms Erdos85.sevenHighT0LowIndexPerm_supportCard
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.relabel
