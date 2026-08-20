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

/-- Missing defects in source fiber `t` whose translation by `delta t`
lands at the residue of target fiber `u`. -/
def sizeTwoCyclicShiftedMissingDefectCount
    {q : ℕ} [NeZero q] {a : ZMod q}
    (missing : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (delta : sizeTwoAllowedDifference q a → ZMod q)
    (t u : sizeTwoAllowedDifference q a) : ℕ := by
  classical
  exact ((Finset.univ : Finset (ZMod q)).filter
    fun x => (missing x t).1 + delta t = u.1).card

/-- A pointwise displacement law identifies duplicate counts with shifted
missing counts. -/
theorem sizeTwoCyclicDuplicateDefectCount_eq_shiftedMissing
    {q : ℕ} [NeZero q] {a : ZMod q}
    (duplicate missing : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (delta : sizeTwoAllowedDifference q a → ZMod q)
    (hdisp : ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a),
      (duplicate x t).1 = (missing x t).1 + delta t)
    (t u : sizeTwoAllowedDifference q a) :
    sizeTwoCyclicDuplicateDefectCount duplicate t u =
      sizeTwoCyclicShiftedMissingDefectCount missing delta t u := by
  classical
  unfold sizeTwoCyclicDuplicateDefectCount
    sizeTwoCyclicShiftedMissingDefectCount
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rw [← hdisp x t]
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    rw [hdisp x t]
    exact hx

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

/-- Displacement-resolved form of sharp-defect circulation.  In the notation
`f_t(u) = Missing(t,u)`, it is the symmetric discrete-derivative equation
`f_t(u-δ_t)-f_t(u) = f_u(t-δ_u)-f_u(t)`, written without subtraction in
`ℕ`. -/
theorem sizeTwoCyclicSharpDefect_cocycle
    {q : ℕ} [NeZero q] {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (duplicate missing : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (delta : sizeTwoAllowedDifference q a → ZMod q)
    (hne : ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a),
      duplicate x t ≠ missing x t)
    (hprofile : ∀ (x : ZMod q) (t u : sizeTwoAllowedDifference q a),
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
        if u = duplicate x t then 2 else if u = missing x t then 0 else 1)
    (hdisp : ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a),
      (duplicate x t).1 = (missing x t).1 + delta t)
    (t u : sizeTwoAllowedDifference q a) :
    sizeTwoCyclicShiftedMissingDefectCount missing delta t u +
        sizeTwoCyclicMissingDefectCount missing u t =
      sizeTwoCyclicShiftedMissingDefectCount missing delta u t +
        sizeTwoCyclicMissingDefectCount missing t u := by
  rw [← sizeTwoCyclicDuplicateDefectCount_eq_shiftedMissing
      duplicate missing delta hdisp t u,
    ← sizeTwoCyclicDuplicateDefectCount_eq_shiftedMissing
      duplicate missing delta hdisp u t]
  exact sizeTwoCyclicSharpDefect_circulation
    code duplicate missing hne hprofile t u

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSharpDefect_circulation
#print axioms Erdos85.sizeTwoCyclicSharpDefect_cocycle
