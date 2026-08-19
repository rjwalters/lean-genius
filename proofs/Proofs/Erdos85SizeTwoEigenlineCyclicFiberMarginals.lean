import Proofs.Erdos85SizeTwoEigenlineCyclicThreeFiberReciprocity

/-!
# Exact q-generic marginals for the displacement-resolved routing tensor

For a fixed source fiber and admissible row displacement, every base point
has exactly one target-difference fiber.  Thus the corresponding incidence
row sums to `q`.  Reciprocity transposes the tensor and supplies the matching
column marginal wherever it is available at both endpoint fibers.
-/

namespace Erdos85

noncomputable section

/-- The disjoint union over target fibers of fixed-displacement darts is
canonically just the set of source base points. -/
def sizeTwoCyclicRoutingFiberRowDartSigmaEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a) (r : ZMod q)
    (hr : t.1 ≠ r ∧ t.1 ≠ r - 1) :
    (Σ s : sizeTwoAllowedDifference q a,
      SizeTwoCyclicRoutingFiberRowDart data t s r) ≃ ZMod q where
  toFun w := w.2.1.base
  invFun x := by
    let row : SizeTwoAdmissibleTargetRow q t.1 := ⟨r, hr⟩
    let s := data.targetDifference x t row
    exact ⟨s, ⟨⟨x, row, rfl⟩, rfl⟩⟩
  left_inv w := by
    rcases w with ⟨s, ⟨⟨x, row, htarget⟩, hrowVal⟩⟩
    have hrow : row = ⟨r, hr⟩ := Subtype.ext hrowVal
    subst row
    subst s
    rfl
  right_inv x := rfl

/-- Exact row marginal of the displacement/fiber incidence tensor. -/
theorem sizeTwoCyclicRoutingFiberRowDart_card_sum_target
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a) (r : ZMod q)
    (hr : t.1 ≠ r ∧ t.1 ≠ r - 1) :
    (∑ s : sizeTwoAllowedDifference q a,
      Fintype.card (SizeTwoCyclicRoutingFiberRowDart data t s r)) = q := by
  rw [← Fintype.card_sigma,
    Fintype.card_congr (sizeTwoCyclicRoutingFiberRowDartSigmaEquiv data t r hr),
    ZMod.card]

/-- Reciprocity turns the row marginal into the corresponding column
marginal.  The hypotheses are deliberately local to the summed fibers. -/
theorem sizeTwoCyclicRoutingFiberRowDart_card_sum_source
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (s : sizeTwoAllowedDifference q a) (r : ZMod q)
    (hsrow : s.1 ≠ -r ∧ s.1 ≠ (-r) - 1)
    (hrecip : ∀ t : sizeTwoAllowedDifference q a, data.ReciprocityAt t) :
    (∑ t : sizeTwoAllowedDifference q a,
      Fintype.card (SizeTwoCyclicRoutingFiberRowDart data t s r)) = q := by
  calc
    _ = ∑ t : sizeTwoAllowedDifference q a,
        Fintype.card (SizeTwoCyclicRoutingFiberRowDart data s t (-r)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact sizeTwoCyclicRoutingFiberRowDart_card_reverse
        (hrecip t) (hrecip s) r
    _ = q := sizeTwoCyclicRoutingFiberRowDart_card_sum_target
      data s (-r) hsrow

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRoutingFiberRowDart_card_sum_target
#print axioms Erdos85.sizeTwoCyclicRoutingFiberRowDart_card_sum_source
