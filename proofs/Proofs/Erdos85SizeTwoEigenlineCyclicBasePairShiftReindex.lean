import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingSecondMomentCensus

/-!
# Reindex distinct cyclic base pairs by nonzero shifts

An ordered pair of distinct bases `(x,y)` has unique coordinates
`(x,d)` with `d = y-x ≠ 0`.  This elementary equivalence is the coordinate
change from source-pair second moments to autocorrelation sums over shifts.
-/

namespace Erdos85

noncomputable section

abbrev SizeTwoCyclicDistinctBasePair (q : ℕ) :=
  {p : ZMod q × ZMod q // p.1 ≠ p.2}

abbrev SizeTwoCyclicBaseNonzeroShift (q : ℕ) :=
  ZMod q × {d : ZMod q // d ≠ 0}

noncomputable instance (q : ℕ) [NeZero q] :
    Fintype (SizeTwoCyclicDistinctBasePair q) :=
  Subtype.fintype _

noncomputable instance (q : ℕ) [NeZero q] :
    Fintype {d : ZMod q // d ≠ 0} :=
  Subtype.fintype _

/-- `(x,y) ↦ (x,y-x)` identifies distinct ordered pairs with a base and a
nonzero cyclic shift. -/
def sizeTwoCyclicDistinctBasePairEquivShift (q : ℕ) :
    SizeTwoCyclicDistinctBasePair q ≃
      SizeTwoCyclicBaseNonzeroShift q where
  toFun p := ⟨p.1.1, ⟨p.1.2 - p.1.1, by
    intro hzero
    apply p.2
    exact (sub_eq_zero.mp hzero).symm⟩⟩
  invFun xd := ⟨(xd.1, xd.1 + xd.2.1), by
    intro heq
    apply xd.2.2
    have h := congrArg (fun z : ZMod q => z - xd.1) heq
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h.symm⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp
  right_inv xd := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp

/-- Generic sum reindexing along the base-pair/shift equivalence. -/
theorem sizeTwoCyclicDistinctBasePair_sum_reindex
    {q : ℕ} [NeZero q] (F : ZMod q → ZMod q → ℕ) :
    (∑ p : SizeTwoCyclicDistinctBasePair q, F p.1.1 p.1.2) =
      ∑ xd : SizeTwoCyclicBaseNonzeroShift q,
        F xd.1 (xd.1 + xd.2.1) := by
  apply Fintype.sum_equiv (sizeTwoCyclicDistinctBasePairEquivShift q)
  intro p
  change F p.1.1 p.1.2 = F p.1.1 (p.1.1 + (p.1.2 - p.1.1))
  congr 1
  abel

/-- Applied to one difference fiber, the ordered source-pair agreement mass
is exactly the sum over bases and nonzero autocorrelation shifts. -/
theorem sizeTwoCyclicAgreement_sum_distinctPairs_eq_sum_shifts
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (t : sizeTwoAllowedDifference q a) :
    (∑ p : SizeTwoCyclicDistinctBasePair q,
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P p.1.1 (p.1.2 - p.1.1) t t)) =
      ∑ xd : SizeTwoCyclicBaseNonzeroShift q,
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a P xd.1 xd.2.1 t t) := by
  simpa using sizeTwoCyclicDistinctBasePair_sum_reindex
    (q := q) (fun x y =>
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P x (y - x) t t))

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicDistinctBasePair_sum_reindex
#print axioms Erdos85.sizeTwoCyclicAgreement_sum_distinctPairs_eq_sum_shifts
