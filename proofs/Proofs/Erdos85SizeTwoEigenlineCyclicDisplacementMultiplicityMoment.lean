import Proofs.Erdos85SizeTwoEigenlineCyclicUniformOrbitObstruction

/-!
# The displacement-resolved fiber moment

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The earlier collision census remembers only the cardinalities with which a
source matching visits the target-difference fibers.  This file restores the
first positional moment: the multiplicities, weighted by their actual cyclic
difference labels, always sum to the punctured-permutation displacement
`2 * (t + 1)`.  Thus any proposed low-collision profile must also solve an
affine equation in `ZMod q`; its duplicate and missing fibers cannot be
placed arbitrarily.
-/

namespace Erdos85

noncomputable section

/-- Number of routes from `(x,t)` whose target lies in difference fiber
`u`.  This is the source-local version of the matching-orbit multiplicity. -/
def sizeTwoCyclicTargetDifferenceMultiplicity
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t u : sizeTwoAllowedDifference q a) : ℕ := by
  classical
  exact ((Finset.univ : Finset (SizeTwoAdmissibleTargetRow q t.1)).filter
    fun r => code.targetDifference x t r = u).card

/-- The local target-difference multiplicities count all `q-2` admissible
rows. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ u : sizeTwoAllowedDifference q a,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u) =
      Fintype.card (SizeTwoAdmissibleTargetRow q t.1) := by
  classical
  simp only [sizeTwoCyclicTargetDifferenceMultiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

/-- Exact displacement-weighted moment of the target-difference
multiplicity vector. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_weighted_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ u : sizeTwoAllowedDifference q a,
      (sizeTwoCyclicTargetDifferenceMultiplicity code x t u : ZMod q) * u.1) =
      2 * (t.1 + 1) := by
  classical
  calc
    (∑ u : sizeTwoAllowedDifference q a,
        (sizeTwoCyclicTargetDifferenceMultiplicity code x t u : ZMod q) * u.1) =
        ∑ r : SizeTwoAdmissibleTargetRow q t.1,
          (code.targetDifference x t r).1 := by
      simp only [sizeTwoCyclicTargetDifferenceMultiplicity, Finset.card_filter,
        Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp
    _ = ∑ r : SizeTwoAdmissibleTargetRow q t.1,
        ((code.toPermutationCode.perm x t r).1 - r.1) := by
      apply Finset.sum_congr rfl
      intro r _
      exact eq_sub_of_add_eq (by
        simpa [add_comm] using code.target_column_eq x t r)
    _ = 2 * (t.1 + 1) :=
      sizeTwoCyclicPermutation_targetDifference_sum hq
        code.toPermutationCode.perm x t

/-- Forced displacement from the missing target fibre to the duplicated
target fibre in a sharp local multiplicity profile. -/
def sizeTwoCyclicSharpDefectDisplacement
    (q : ℕ) [NeZero q] (t : ZMod q) : ZMod q :=
  2 * (t + 1) - (((q * (q - 1) / 2 : ℕ) : ZMod q) + 1)

/-- Forced sharp-defect displacements are reversed by the allowed-fibre
reflection `t ↦ -1-t`. -/
theorem sizeTwoCyclicSharpDefectDisplacement_reflection
    (q : ℕ) [NeZero q] (t : ZMod q) :
    sizeTwoCyclicSharpDefectDisplacement q (-1 - t) =
      -sizeTwoCyclicSharpDefectDisplacement q t := by
  have htriNat :
      2 * (q * (q - 1) / 2) = q * (q - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self q)
  have htri :
      (2 : ZMod q) * ((q * (q - 1) / 2 : ℕ) : ZMod q) = 0 := by
    calc
      (2 : ZMod q) * ((q * (q - 1) / 2 : ℕ) : ZMod q) =
          ((2 * (q * (q - 1) / 2) : ℕ) : ZMod q) := by norm_num
      _ = ((q * (q - 1) : ℕ) : ZMod q) := by rw [htriNat]
      _ = 0 := by simp
  unfold sizeTwoCyclicSharpDefectDisplacement
  have htri' :
      ((q * (q - 1) / 2 : ℕ) : ZMod q) * 2 = 0 := by
    simpa [mul_comm] using htri
  linear_combination -htri'

/-- The exact affine moment of the deviation from the all-ones profile.
For a minimum-collision profile (one duplicated fiber and one missing fiber),
the left side reduces to `duplicate - missing`; this is the positional
constraint absent from the aggregate collision ledger. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_deviation_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (ha : a ≠ -1 - a)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ u : sizeTwoAllowedDifference q a,
        (sizeTwoCyclicTargetDifferenceMultiplicity code x t u : ZMod q) * u.1) -
      (∑ u : sizeTwoAllowedDifference q a, u.1) =
        2 * (t.1 + 1) -
          (((q * (q - 1) / 2 : ℕ) : ZMod q) + 1) := by
  rw [sizeTwoCyclicTargetDifferenceMultiplicity_weighted_sum hq code x t,
    sizeTwoAllowedDifference_sum q a ha]

/-- At even order, the weighted deviations from the all-ones profiles on a
reflected pair of source fibres are additive inverses.  This is the defect
form of the constant reflection-pair displacement charge. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_reflectionPair_deviation_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (ha : a ≠ -1 - a)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    ((∑ u : sizeTwoAllowedDifference q a,
        (sizeTwoCyclicTargetDifferenceMultiplicity code x t u : ZMod q) * u.1) -
      (∑ u : sizeTwoAllowedDifference q a, u.1)) +
    ((∑ u : sizeTwoAllowedDifference q a,
        (sizeTwoCyclicTargetDifferenceMultiplicity code x
          (sizeTwoAllowedDifferenceReflection q a t) u : ZMod q) * u.1) -
      (∑ u : sizeTwoAllowedDifference q a, u.1)) = 0 := by
  rw [sizeTwoCyclicTargetDifferenceMultiplicity_deviation_sum hq ha,
    sizeTwoCyclicTargetDifferenceMultiplicity_deviation_sum hq ha,
    sizeTwoAllowedDifferenceReflection_val]
  have htriNat :
      2 * (q * (q - 1) / 2) = q * (q - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self q)
  have htri :
      (2 : ZMod q) * ((q * (q - 1) / 2 : ℕ) : ZMod q) = 0 := by
    calc
      (2 : ZMod q) * ((q * (q - 1) / 2 : ℕ) : ZMod q) =
          ((2 * (q * (q - 1) / 2) : ℕ) : ZMod q) := by norm_num
      _ = ((q * (q - 1) : ℕ) : ZMod q) := by rw [htriNat]
      _ = 0 := by simp
  have htri' :
      ((q * (q - 1) / 2 : ℕ) : ZMod q) * 2 = 0 := by
    simpa [mul_comm] using htri
  calc
    _ = -(((q * (q - 1) / 2 : ℕ) : ZMod q) * 2) := by ring
    _ = 0 := by rw [htri']; simp

/-- In the sharp one-collision regime, a row has one duplicated target
fiber and one missing target fiber.  Their cyclic displacement is forced by
the source fiber.  This is the concrete positional datum that reciprocity
must couple between different rows. -/
theorem sizeTwoCyclic_singleDuplicateMissing_displacement
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (ha : a ≠ -1 - a)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t duplicate missing : sizeTwoAllowedDifference q a)
    (hne : duplicate ≠ missing)
    (hprofile : ∀ u : sizeTwoAllowedDifference q a,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
        if u = duplicate then 2 else if u = missing then 0 else 1) :
    duplicate.1 - missing.1 =
      2 * (t.1 + 1) -
        (((q * (q - 1) / 2 : ℕ) : ZMod q) + 1) := by
  classical
  have hdev := sizeTwoCyclicTargetDifferenceMultiplicity_deviation_sum
    hq ha code x t
  have hleft :
      (∑ u : sizeTwoAllowedDifference q a,
          (sizeTwoCyclicTargetDifferenceMultiplicity code x t u : ZMod q) * u.1) -
        (∑ u : sizeTwoAllowedDifference q a, u.1) =
          duplicate.1 - missing.1 := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ u : sizeTwoAllowedDifference q a,
          ((sizeTwoCyclicTargetDifferenceMultiplicity code x t u : ZMod q) * u.1 -
            u.1)) =
          ∑ u : sizeTwoAllowedDifference q a,
            if u = duplicate then duplicate.1
            else if u = missing then -missing.1 else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [hprofile u]
        by_cases hud : u = duplicate
        · subst u
          simp
          ring
        · by_cases hum : u = missing
          · subst u
            simp [hud]
          · simp [hud, hum]
      _ = duplicate.1 - missing.1 := by
        rw [show (∑ u : sizeTwoAllowedDifference q a,
            if u = duplicate then duplicate.1
            else if u = missing then -missing.1 else 0) =
              (∑ u : sizeTwoAllowedDifference q a,
                if u = duplicate then duplicate.1 else 0) +
              ∑ u : sizeTwoAllowedDifference q a,
                if u = missing then -missing.1 else 0 by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro u _
          by_cases hud : u = duplicate
          · subst u
            simp [hne]
          · simp [hud]]
        simp [sub_eq_add_neg]
  rw [hleft] at hdev
  exact hdev

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_sum
#print axioms Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_weighted_sum
#print axioms Erdos85.sizeTwoCyclicSharpDefectDisplacement_reflection
#print axioms Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_deviation_sum
#print axioms Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_reflectionPair_deviation_sum
#print axioms Erdos85.sizeTwoCyclic_singleDuplicateMissing_displacement
