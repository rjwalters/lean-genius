import Proofs.Erdos85SizeTwoEigenlineCyclicBasePairShiftReindex
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Data.Sym.Card

/-!
# Ordered-pair form of the incidence second moment

For every target of multiplicity `m`, its ordered pairs of distinct incident
sources have cardinality `2 * C(m,2)`.  Transposing this incidence count gives
the exact factor-two bridge from target cherries to common-target counts over
ordered source pairs.
-/

namespace Erdos85

noncomputable section

/-- Exact ordered-pair incidence transpose. -/
theorem two_mul_sum_choose_two_pointsOn_eq_sum_offDiag_commonTargets
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (P : Finset α) (L : Finset β) :
    2 * (∑ l ∈ L, (Erdos101OQ02ST.pointsOn Inc P l).card.choose 2) =
      ∑ p ∈ P.offDiag,
        (L.filter fun l => Inc p.1 l ∧ Inc p.2 l).card := by
  classical
  rw [Finset.mul_sum]
  calc
    (∑ l ∈ L, 2 * (Erdos101OQ02ST.pointsOn Inc P l).card.choose 2) =
        ∑ l ∈ L,
          ((Erdos101OQ02ST.pointsOn Inc P l).offDiag).card := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [← Sym2.card_image_offDiag
        (Erdos101OQ02ST.pointsOn Inc P l)]
      exact Sym2.two_mul_card_image_offDiag
        (Erdos101OQ02ST.pointsOn Inc P l)
    _ = ∑ l ∈ L,
        ((P.offDiag).filter fun p => Inc p.1 l ∧ Inc p.2 l).card := by
      apply Finset.sum_congr rfl
      intro l hl
      congr 1
      ext p
      simp [Erdos101OQ02ST.pointsOn, Finset.mem_offDiag]
      aesop
    _ = ∑ l ∈ L, ∑ p ∈ P.offDiag,
          if Inc p.1 l ∧ Inc p.2 l then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.card_filter]
    _ = ∑ p ∈ P.offDiag, ∑ l ∈ L,
          if Inc p.1 l ∧ Inc p.2 l then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P.offDiag,
        (L.filter fun l => Inc p.1 l ∧ Inc p.2 l).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.card_filter]

/-- Fixed-orbit specialization: twice the target-multiplicity cherry mass is
the sum of common matching-edge counts over ordered distinct bases. -/
theorem two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    2 * (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) =
      ∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
        (sizeTwoCyclicSourceMatching code (p.1, t) ∩
          sizeTwoCyclicSourceMatching code (p.2, t)).card := by
  classical
  let Inc : ZMod q → SizeTwoCyclicAbsoluteGridEdge q → Prop :=
    fun x e => e ∈ sizeTwoCyclicSourceMatching code (x, t)
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
        ((Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).filter
          fun e => e ∈ sizeTwoCyclicSourceMatching code (p.1, t) ∧
            e ∈ sizeTwoCyclicSourceMatching code (p.2, t)).card := by
      simpa [Inc, Erdos101OQ02ST.pointsOn,
        sizeTwoCyclicMatchingOrbitMultiplicity] using
        (two_mul_sum_choose_two_pointsOn_eq_sum_offDiag_commonTargets Inc
          (Finset.univ : Finset (ZMod q))
          (Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      ext e
      simp

/-- **Exact orbit autocorrelation identity.**  Twice the target-multiplicity
cherry mass equals the total shifted-agreement mass over all bases and all
nonzero shifts. -/
theorem two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_eq_agreement_shifts
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    2 * (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) =
      ∑ xd : SizeTwoCyclicBaseNonzeroShift q,
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
          code.toReciprocalCode.toPermutationCode.perm
          xd.1 xd.2.1 t t) := by
  classical
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
        (sizeTwoCyclicSourceMatching code (p.1, t) ∩
          sizeTwoCyclicSourceMatching code (p.2, t)).card :=
      two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum code t
    _ = ∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
          code.toReciprocalCode.toPermutationCode.perm
          p.1 (p.2 - p.1) t t) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sizeTwoCyclicSourceMatching_inter_card_eq_agreement
        code (p.1, t) (p.2, t)
    _ = ∑ p : SizeTwoCyclicDistinctBasePair q,
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
          code.toReciprocalCode.toPermutationCode.perm
          p.1.1 (p.1.2 - p.1.1) t t) := by
      rw [Finset.sum_subtype
        ((Finset.univ : Finset (ZMod q)).offDiag)
        (p := fun p : ZMod q × ZMod q => p.1 ≠ p.2)
        (fun p => by simp [Finset.mem_offDiag])]
    _ = _ := sizeTwoCyclicAgreement_sum_distinctPairs_eq_sum_shifts
      code.toReciprocalCode.toPermutationCode.perm t

end

end Erdos85

#print axioms Erdos85.two_mul_sum_choose_two_pointsOn_eq_sum_offDiag_commonTargets
#print axioms Erdos85.two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum
#print axioms Erdos85.two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_eq_agreement_shifts
