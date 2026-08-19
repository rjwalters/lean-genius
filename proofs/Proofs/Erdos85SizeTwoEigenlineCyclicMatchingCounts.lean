import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingDesign
import Proofs.Erdos85SizeTwoEigenlineCyclicQuotient

/-!
# Exact counts for the cyclic matching design

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

This file records the numerical parameters of the absolute matching design:
there are `q(q-2)` source blocks, every block has `q-2` points, and hence
the total number of source-point incidences is `q(q-2)^2`.  Together with
the pairwise-intersection bound from `CyclicMatchingDesign`, these are the
inputs for packing and second-moment arguments.
-/

namespace Erdos85

noncomputable section

/-- Exactly two relative target rows are forbidden when `1 ≠ 0` in
`ZMod q`. -/
theorem sizeTwoAdmissibleTargetRow_card
    (q : ℕ) [NeZero q] (t : ZMod q) (hq1 : (1 : ZMod q) ≠ 0) :
    Fintype.card (SizeTwoAdmissibleTargetRow q t) = q - 2 := by
  classical
  change Fintype.card {r : ZMod q // t ≠ r ∧ t ≠ r - 1} = q - 2
  have htne : t ≠ t + 1 := by
    intro h
    apply hq1
    have hz := congrArg (fun z : ZMod q => z - t) h
    simpa using hz.symm
  let normalize : {r : ZMod q // t ≠ r ∧ t ≠ r - 1} ≃
      {r : ZMod q // r ≠ t ∧ r ≠ t + 1} :=
    { toFun := fun r => ⟨r.1, r.2.1.symm, by
        intro hr
        apply r.2.2
        rw [hr]
        simp⟩
      invFun := fun r => ⟨r.1, r.2.1.symm, by
        intro hr
        apply r.2.2
        have hz := congrArg (fun z : ZMod q => z + 1) hr
        simpa [sub_eq_add_neg, add_assoc] using hz.symm⟩
      left_inv := fun r => by apply Subtype.ext; rfl
      right_inv := fun r => by apply Subtype.ext; rfl }
  rw [Fintype.card_congr normalize, Fintype.card_subtype]
  rw [show ({r : ZMod q | r ≠ t ∧ r ≠ t + 1} : Finset (ZMod q)) =
      Finset.univ \ {t, t + 1} by
    ext r
    simp [not_or]]
  simp [Finset.card_sdiff, ZMod.card, htne]

/-- Every source matching has exactly `q-2` absolute grid edges. -/
theorem sizeTwoCyclicSourceMatching_card_eq_sub_two
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (source : SizeTwoCyclicMatchingSource q a) :
    (sizeTwoCyclicSourceMatching code source).card = q - 2 := by
  rw [sizeTwoCyclicSourceMatching_card,
    sizeTwoAdmissibleTargetRow_card q source.2.1 hq1]

/-- The cyclic matching design has one source block for every exterior
cell, hence `q(q-2)` blocks. -/
theorem sizeTwoCyclicMatchingSource_card
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : a ≠ -1 - a) :
    Fintype.card (SizeTwoCyclicMatchingSource q a) = q * (q - 2) := by
  rw [Fintype.card_prod, ZMod.card,
    sizeTwoAllowedDifference_card q a ha]

/-- Exact total incidence count of sources against their matching edges. -/
theorem sizeTwoCyclicSourceMatching_total_card
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0) :
    (∑ source : SizeTwoCyclicMatchingSource q a,
        (sizeTwoCyclicSourceMatching code source).card) =
      q * (q - 2) * (q - 2) := by
  simp_rw [sizeTwoCyclicSourceMatching_card_eq_sub_two code hq1]
  rw [Finset.sum_const, Finset.card_univ,
    sizeTwoCyclicMatchingSource_card q a ha]
  simp

end

end Erdos85

#print axioms Erdos85.sizeTwoAdmissibleTargetRow_card
#print axioms Erdos85.sizeTwoCyclicSourceMatching_total_card
