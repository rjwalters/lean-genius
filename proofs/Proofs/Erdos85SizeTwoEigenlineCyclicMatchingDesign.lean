import Proofs.Erdos85SizeTwoEigenlineCyclicCrossAgreement

/-!
# Absolute matching design of a full cyclic permutation code

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

Each exterior source gives a matching in the absolute `q × q` row/column
grid.  Cross-difference agreement says distinct source matchings share at
most one grid edge.
-/

namespace Erdos85

noncomputable section

noncomputable instance sizeTwoAdmissibleTargetRowFintype
    (q : ℕ) [NeZero q] (t : ZMod q) :
    Fintype (SizeTwoAdmissibleTargetRow q t) := Subtype.fintype _

abbrev SizeTwoCyclicMatchingSource (q : ℕ) (a : ZMod q) :=
  ZMod q × sizeTwoAllowedDifference q a

abbrev SizeTwoCyclicAbsoluteGridEdge (q : ℕ) := ZMod q × ZMod q

def sizeTwoCyclicMatchingEdge
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source : SizeTwoCyclicMatchingSource q a)
    (r : SizeTwoAdmissibleTargetRow q source.2.1) :
    SizeTwoCyclicAbsoluteGridEdge q :=
  (source.1 + r.1,
    source.1 + (code.toReciprocalCode.toPermutationCode.perm
      source.1 source.2 r).1)

theorem sizeTwoCyclicMatchingEdge_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source : SizeTwoCyclicMatchingSource q a) :
    Function.Injective (sizeTwoCyclicMatchingEdge code source) := by
  intro r s hrs
  apply Subtype.ext
  have hfirst := congrArg Prod.fst hrs
  exact add_left_cancel hfirst

def sizeTwoCyclicSourceMatching
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source : SizeTwoCyclicMatchingSource q a) :
    Finset (SizeTwoCyclicAbsoluteGridEdge q) :=
  Finset.univ.image (sizeTwoCyclicMatchingEdge code source)

theorem sizeTwoCyclicSourceMatching_card
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source : SizeTwoCyclicMatchingSource q a) :
    (sizeTwoCyclicSourceMatching code source).card =
      Fintype.card (SizeTwoAdmissibleTargetRow q source.2.1) := by
  classical
  unfold sizeTwoCyclicSourceMatching
  rw [Finset.card_image_of_injective _
    (sizeTwoCyclicMatchingEdge_injective code source)]
  exact Finset.card_univ

theorem sizeTwoCyclicSourceMatching_mem_iff
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source : SizeTwoCyclicMatchingSource q a)
    (e : SizeTwoCyclicAbsoluteGridEdge q) :
    e ∈ sizeTwoCyclicSourceMatching code source ↔
      ∃ r : SizeTwoAdmissibleTargetRow q source.2.1,
        sizeTwoCyclicMatchingEdge code source r = e := by
  classical
  simp [sizeTwoCyclicSourceMatching]

def sizeTwoCyclicMatchingIntersectionRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicSourceMatching code source₁ ∩
        sizeTwoCyclicSourceMatching code source₂}) :
    SizeTwoAdmissibleTargetRow q source₁.2.1 :=
  Classical.choose ((sizeTwoCyclicSourceMatching_mem_iff code source₁ e.1).mp
    (Finset.mem_inter.mp e.2).1)

theorem sizeTwoCyclicMatchingIntersectionRow_spec
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicSourceMatching code source₁ ∩
        sizeTwoCyclicSourceMatching code source₂}) :
    sizeTwoCyclicMatchingEdge code source₁
      (sizeTwoCyclicMatchingIntersectionRow code source₁ source₂ e) = e.1 :=
  Classical.choose_spec ((sizeTwoCyclicSourceMatching_mem_iff code source₁ e.1).mp
    (Finset.mem_inter.mp e.2).1)

def sizeTwoCyclicMatchingIntersectionSecondRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicSourceMatching code source₁ ∩
        sizeTwoCyclicSourceMatching code source₂}) :
    SizeTwoAdmissibleTargetRow q source₂.2.1 :=
  Classical.choose ((sizeTwoCyclicSourceMatching_mem_iff code source₂ e.1).mp
    (Finset.mem_inter.mp e.2).2)

theorem sizeTwoCyclicMatchingIntersectionSecondRow_spec
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicSourceMatching code source₁ ∩
        sizeTwoCyclicSourceMatching code source₂}) :
    sizeTwoCyclicMatchingEdge code source₂
      (sizeTwoCyclicMatchingIntersectionSecondRow code source₁ source₂ e) = e.1 :=
  Classical.choose_spec ((sizeTwoCyclicSourceMatching_mem_iff code source₂ e.1).mp
    (Finset.mem_inter.mp e.2).2)

def sizeTwoCyclicMatchingIntersectionAgreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicSourceMatching code source₁ ∩
        sizeTwoCyclicSourceMatching code source₂}) :
    SizeTwoCrossShiftedPermutationAgreement q a
      code.toReciprocalCode.toPermutationCode.perm
      source₁.1 (source₂.1 - source₁.1) source₁.2 source₂.2 := by
  classical
  let r₁ := sizeTwoCyclicMatchingIntersectionRow code source₁ source₂ e
  let r₂ := sizeTwoCyclicMatchingIntersectionSecondRow code source₁ source₂ e
  have hr₁ := sizeTwoCyclicMatchingIntersectionRow_spec code source₁ source₂ e
  have hr₂ := sizeTwoCyclicMatchingIntersectionSecondRow_spec code source₁ source₂ e
  have hedge : sizeTwoCyclicMatchingEdge code source₁ r₁ =
      sizeTwoCyclicMatchingEdge code source₂ r₂ := hr₁.trans hr₂.symm
  have hrow : r₂.1 = r₁.1 - (source₂.1 - source₁.1) := by
    have h := congrArg Prod.fst hedge
    dsimp [sizeTwoCyclicMatchingEdge] at h
    calc
      r₂.1 = -source₂.1 + (source₂.1 + r₂.1) := by abel
      _ = -source₂.1 + (source₁.1 + r₁.1) := by rw [← h]
      _ = r₁.1 - (source₂.1 - source₁.1) := by abel
  refine ⟨r₁, ?_, ?_⟩
  · simpa [← hrow] using r₂.2
  · have h := congrArg Prod.snd hedge
    have hr₂eq : r₂ =
        ⟨r₁.1 - (source₂.1 - source₁.1), by
          simpa [← hrow] using r₂.2⟩ := Subtype.ext hrow
    rw [← hr₂eq]
    simpa [sizeTwoCyclicMatchingEdge, add_assoc] using h

theorem sizeTwoCyclicMatchingIntersectionAgreement_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a) :
    Function.Injective
      (sizeTwoCyclicMatchingIntersectionAgreement code source₁ source₂) := by
  classical
  intro e f hef
  apply Subtype.ext
  rw [← sizeTwoCyclicMatchingIntersectionRow_spec code source₁ source₂ e,
    ← sizeTwoCyclicMatchingIntersectionRow_spec code source₁ source₂ f]
  exact congrArg (sizeTwoCyclicMatchingEdge code source₁)
    (by
      simpa [sizeTwoCyclicMatchingIntersectionAgreement] using
        congrArg (fun w => w.row) hef)

theorem sizeTwoCyclicSourceMatching_inter_card_le_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (hne : source₁ ≠ source₂) :
    (sizeTwoCyclicSourceMatching code source₁ ∩
      sizeTwoCyclicSourceMatching code source₂).card ≤ 1 := by
  classical
  let d := source₂.1 - source₁.1
  have hdiff : d ≠ 0 ∨ source₁.2 ≠ source₂.2 := by
    by_cases hd : d = 0
    · right
      intro ht
      apply hne
      apply Prod.ext
      · dsimp [d] at hd
        have := congrArg (fun z : ZMod q => z + source₁.1) hd
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this.symm
      · exact ht
    · exact Or.inl hd
  calc
    (sizeTwoCyclicSourceMatching code source₁ ∩
        sizeTwoCyclicSourceMatching code source₂).card =
        Fintype.card {e : SizeTwoCyclicAbsoluteGridEdge q //
          e ∈ sizeTwoCyclicSourceMatching code source₁ ∩
            sizeTwoCyclicSourceMatching code source₂} := by
      exact (Fintype.card_coe _).symm
    _ ≤ Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
        code.toReciprocalCode.toPermutationCode.perm
        source₁.1 d source₁.2 source₂.2) :=
      Fintype.card_le_of_injective
        (sizeTwoCyclicMatchingIntersectionAgreement code source₁ source₂)
        (sizeTwoCyclicMatchingIntersectionAgreement_injective
          code source₁ source₂)
    _ ≤ 1 := code.cross_agreement_le_one
      source₁.1 d source₁.2 source₂.2 hdiff

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSourceMatching_card
#print axioms Erdos85.sizeTwoCyclicSourceMatching_inter_card_le_one
