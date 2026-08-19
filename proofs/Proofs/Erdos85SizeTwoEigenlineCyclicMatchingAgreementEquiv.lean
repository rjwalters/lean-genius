import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingDesign

/-!
# Matching intersections are exactly shifted agreements

The matching-design API previously embedded a common absolute grid edge into
a shifted-permutation agreement.  The map is also surjective: an agreement
itself specifies the common absolute edge.  This exact equivalence lets
second-moment counts on matching intersections be transported without losing
mass to the permutation-code autocorrelation language.
-/

namespace Erdos85

noncomputable section

/-- The absolute edge specified by a shifted agreement belongs to both source
matchings. -/
def sizeTwoCyclicAgreementIntersectionEdge
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (w : SizeTwoCrossShiftedPermutationAgreement q a
      code.toReciprocalCode.toPermutationCode.perm
      source₁.1 (source₂.1 - source₁.1) source₁.2 source₂.2) :
    {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicSourceMatching code source₁ ∩
        sizeTwoCyclicSourceMatching code source₂} := by
  let r₂ : SizeTwoAdmissibleTargetRow q source₂.2.1 :=
    ⟨w.row.1 - (source₂.1 - source₁.1), w.shifted_admissible⟩
  refine ⟨sizeTwoCyclicMatchingEdge code source₁ w.row, ?_⟩
  apply Finset.mem_inter.mpr
  constructor
  · exact (sizeTwoCyclicSourceMatching_mem_iff code source₁ _).mpr
      ⟨w.row, rfl⟩
  · exact (sizeTwoCyclicSourceMatching_mem_iff code source₂ _).mpr
      ⟨r₂, by
        apply Prod.ext
        · dsimp [sizeTwoCyclicMatchingEdge, r₂]
          abel
        · dsimp [sizeTwoCyclicMatchingEdge, r₂]
          have h := w.column_eq
          simpa [add_assoc] using h.symm⟩

theorem sizeTwoCyclicMatchingIntersectionAgreement_surjective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a) :
    Function.Surjective
      (sizeTwoCyclicMatchingIntersectionAgreement code source₁ source₂) := by
  intro w
  let e := sizeTwoCyclicAgreementIntersectionEdge code source₁ source₂ w
  refine ⟨e, ?_⟩
  apply SizeTwoCrossShiftedPermutationAgreement.row_injective
  apply (sizeTwoCyclicMatchingEdge_injective code source₁)
  change sizeTwoCyclicMatchingEdge code source₁
      (sizeTwoCyclicMatchingIntersectionRow code source₁ source₂ e) =
    sizeTwoCyclicMatchingEdge code source₁ w.row
  rw [sizeTwoCyclicMatchingIntersectionRow_spec code source₁ source₂ e]
  rfl

/-- Exact equivalence between common matching edges and shifted agreements. -/
def sizeTwoCyclicMatchingIntersectionAgreementEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a) :
    {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicSourceMatching code source₁ ∩
        sizeTwoCyclicSourceMatching code source₂} ≃
      SizeTwoCrossShiftedPermutationAgreement q a
        code.toReciprocalCode.toPermutationCode.perm
        source₁.1 (source₂.1 - source₁.1) source₁.2 source₂.2 :=
  Equiv.ofBijective
    (sizeTwoCyclicMatchingIntersectionAgreement code source₁ source₂)
    ⟨sizeTwoCyclicMatchingIntersectionAgreement_injective
        code source₁ source₂,
      sizeTwoCyclicMatchingIntersectionAgreement_surjective
        code source₁ source₂⟩

/-- The autocorrelation count is exactly the matching-intersection size. -/
theorem sizeTwoCyclicSourceMatching_inter_card_eq_agreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a) :
    (sizeTwoCyclicSourceMatching code source₁ ∩
      sizeTwoCyclicSourceMatching code source₂).card =
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
        code.toReciprocalCode.toPermutationCode.perm
        source₁.1 (source₂.1 - source₁.1) source₁.2 source₂.2) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr
    (sizeTwoCyclicMatchingIntersectionAgreementEquiv code source₁ source₂)

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicMatchingIntersectionAgreement_surjective
#print axioms Erdos85.sizeTwoCyclicSourceMatching_inter_card_eq_agreement
