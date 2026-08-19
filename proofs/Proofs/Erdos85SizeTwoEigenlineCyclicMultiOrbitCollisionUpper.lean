import Proofs.Erdos85SizeTwoEigenlineCyclicCrossOrbitCollisionBound
import Proofs.Erdos85SizeTwoEigenlineCyclicOrderedPairSecondMoment

/-!
# Explicit multi-orbit collision upper envelope

The within-orbit part of the selected collision mass is also controlled by
the matching-design intersection law.  Combining it with the cross-orbit
bound leaves a purely numerical upper envelope for any selected set of
difference orbits.
-/

namespace Erdos85

noncomputable section

/-- Within one difference orbit, twice the collision mass is at most the
number `q(q-1)` of ordered distinct source pairs. -/
theorem two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    2 * (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) ≤
      q * (q - 1) := by
  classical
  rw [two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum]
  calc
    (∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
      (sizeTwoCyclicSourceMatching code (p.1, t) ∩
        sizeTwoCyclicSourceMatching code (p.2, t)).card) ≤
        ∑ _p ∈ (Finset.univ : Finset (ZMod q)).offDiag, 1 := by
      apply Finset.sum_le_sum
      intro p hp
      apply sizeTwoCyclicSourceMatching_inter_card_le_one
      intro h
      exact (Finset.mem_offDiag.mp hp).2.2 (congrArg Prod.fst h)
    _ = q * (q - 1) := by
      simp
      rw [Nat.mul_sub_left_distrib]
      simp

/-- Sum of all within-orbit collision masses over a selected orbit set. -/
theorem two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_selected_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    (∑ t ∈ T, 2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) ≤
      T.card * (q * (q - 1)) := by
  calc
    _ ≤ ∑ _t ∈ T, q * (q - 1) := by
      apply Finset.sum_le_sum
      intro t ht
      exact two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_le
        code t
    _ = T.card * (q * (q - 1)) := by simp

/-- Fully numerical selected-orbit collision upper envelope. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_numerical_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2 ≤
      T.card * (q * (q - 1)) + T.offDiag.card * (q * q) := by
  exact le_trans
    (sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_le code T)
    (Nat.add_le_add_right
      (two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_selected_le
        code T) _)

end

end Erdos85

#print axioms Erdos85.two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_le
#print axioms Erdos85.two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_selected_le
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_numerical_le
