import Proofs.Erdos85SizeTwoEigenlineCyclicTargetFiberReciprocity

/-!
# Circulation law for sharp duplicate/missing defects

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

When every local target-fiber vector has the sharp one-duplicate/one-missing
shape, aggregate route reciprocity forces a transpose law on the directed
defects.  This is the first cross-row constraint that refers directly to the
exceptional fibers extracted from collision mass one.
-/

namespace Erdos85

noncomputable section

/-- Number of source bases in fiber `t` whose sharp profile duplicates
target fiber `u`. -/
def sizeTwoCyclicDuplicateDefectCount
    {q : ℕ} [NeZero q] {a : ZMod q}
    (duplicate : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (t u : sizeTwoAllowedDifference q a) : ℕ := by
  classical
  exact ((Finset.univ : Finset (ZMod q)).filter
    fun x => duplicate x t = u).card

/-- Number of source bases in fiber `t` whose sharp profile misses target
fiber `u`. -/
def sizeTwoCyclicMissingDefectCount
    {q : ℕ} [NeZero q] {a : ZMod q}
    (missing : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (t u : sizeTwoAllowedDifference q a) : ℕ := by
  classical
  exact ((Finset.univ : Finset (ZMod q)).filter
    fun x => missing x t = u).card

/-- Reciprocity makes sharp duplicate/missing defects into a circulation:
`duplicates(t,u) + missing(u,t)` is symmetric in `t,u`. -/
theorem sizeTwoCyclicSharpDefect_circulation
    {q : ℕ} [NeZero q] {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (duplicate missing : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (hne : ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a),
      duplicate x t ≠ missing x t)
    (hprofile : ∀ (x : ZMod q) (t u : sizeTwoAllowedDifference q a),
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
        if u = duplicate x t then 2 else if u = missing x t then 0 else 1)
    (t u : sizeTwoAllowedDifference q a) :
    sizeTwoCyclicDuplicateDefectCount duplicate t u +
        sizeTwoCyclicMissingDefectCount missing u t =
      sizeTwoCyclicDuplicateDefectCount duplicate u t +
        sizeTwoCyclicMissingDefectCount missing t u := by
  classical
  have hrow (s v : sizeTwoAllowedDifference q a) :
      (∑ x : ZMod q,
          sizeTwoCyclicTargetDifferenceMultiplicity code x s v) +
        sizeTwoCyclicMissingDefectCount missing s v =
          q + sizeTwoCyclicDuplicateDefectCount duplicate s v := by
    unfold sizeTwoCyclicMissingDefectCount sizeTwoCyclicDuplicateDefectCount
    rw [Finset.card_filter, Finset.card_filter]
    conv_rhs =>
      lhs
      rw [show q = ∑ _x : ZMod q, 1 by simp [ZMod.card]]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [hprofile x s v]
    by_cases hd : v = duplicate x s
    · simp [hd, eq_comm, hne x s]
    · by_cases hm : v = missing x s
      · simp [hm, eq_comm, hne x s]
      · simp [hd, hm, eq_comm]
  have htu := hrow t u
  have hut := hrow u t
  have hsym := sizeTwoCyclicTargetDifferenceMultiplicity_sum_symm code t u
  omega

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSharpDefect_circulation
