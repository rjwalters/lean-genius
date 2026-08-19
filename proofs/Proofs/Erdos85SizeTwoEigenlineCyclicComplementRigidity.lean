import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedOrbitComplement

/-!
# Equality rigidity for complementary cyclic fibers

At `q = 8`, a selected family and its complement have multiplicities summing
to six at every allowed source-cell.  The convexity of `n.choose 2` then says
that their combined local collision mass is minimized uniquely by the balanced
split `3 + 3`.  This packages the equality case needed to turn a sharp global
collision upper bound into pointwise fiber classification.
-/

namespace Erdos85

noncomputable section

private theorem choose_two_add_choose_two_ge_six_of_add_eq_six
    {x y : ℕ} (hxy : x + y = 6) :
    6 ≤ x.choose 2 + y.choose 2 := by
  have hx : x ≤ 6 := by omega
  have hy : y = 6 - x := by omega
  rw [hy]
  interval_cases x <;> norm_num [Nat.choose]

private theorem choose_two_add_choose_two_eq_six_iff_of_add_eq_six
    {x y : ℕ} (hxy : x + y = 6) :
    x.choose 2 + y.choose 2 = 6 ↔ x = 3 := by
  have hx : x ≤ 6 := by omega
  have hy : y = 6 - x := by omega
  rw [hy]
  interval_cases x <;> norm_num [Nat.choose]

/-- Selected and complementary fibers contribute at least six local
collisions at every allowed source-cell. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_ge_six
    (code : SizeTwoCyclicFullPermutationCode 8 (1 : ZMod 8))
    (T : Finset (sizeTwoAllowedDifference 8 (1 : ZMod 8)))
    (target : SizeTwoCyclicMatchingSource 8 (1 : ZMod 8)) :
    6 ≤
      (sizeTwoCyclicSelectedOrbitMultiplicity code T
          (sizeTwoCyclicMatchingSourceCell target)).choose 2 +
        (sizeTwoCyclicSelectedOrbitMultiplicity code
          (sizeTwoAllowedDifferenceComplement T)
          (sizeTwoCyclicMatchingSourceCell target)).choose 2 := by
  apply choose_two_add_choose_two_ge_six_of_add_eq_six
  simpa using sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_add_compl
    code (by decide) T target

/-- Equality in the local complementary collision bound occurs exactly at the
balanced `3 + 3` split. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_eq_six_iff
    (code : SizeTwoCyclicFullPermutationCode 8 (1 : ZMod 8))
    (T : Finset (sizeTwoAllowedDifference 8 (1 : ZMod 8)))
    (target : SizeTwoCyclicMatchingSource 8 (1 : ZMod 8)) :
    (sizeTwoCyclicSelectedOrbitMultiplicity code T
          (sizeTwoCyclicMatchingSourceCell target)).choose 2 +
        (sizeTwoCyclicSelectedOrbitMultiplicity code
          (sizeTwoAllowedDifferenceComplement T)
          (sizeTwoCyclicMatchingSourceCell target)).choose 2 = 6 ↔
      sizeTwoCyclicSelectedOrbitMultiplicity code T
        (sizeTwoCyclicMatchingSourceCell target) = 3 := by
  apply choose_two_add_choose_two_eq_six_iff_of_add_eq_six
  simpa using sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_add_compl
    code (by decide) T target

/-- Any unbalanced selected/complementary split costs at least seven local
collisions. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_ge_seven
    (code : SizeTwoCyclicFullPermutationCode 8 (1 : ZMod 8))
    (T : Finset (sizeTwoAllowedDifference 8 (1 : ZMod 8)))
    (target : SizeTwoCyclicMatchingSource 8 (1 : ZMod 8))
    (hunbalanced : sizeTwoCyclicSelectedOrbitMultiplicity code T
      (sizeTwoCyclicMatchingSourceCell target) ≠ 3) :
    7 ≤
      (sizeTwoCyclicSelectedOrbitMultiplicity code T
          (sizeTwoCyclicMatchingSourceCell target)).choose 2 +
        (sizeTwoCyclicSelectedOrbitMultiplicity code
          (sizeTwoAllowedDifferenceComplement T)
          (sizeTwoCyclicMatchingSourceCell target)).choose 2 := by
  have hge :=
    sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_ge_six
      code T target
  have hne :
      (sizeTwoCyclicSelectedOrbitMultiplicity code T
            (sizeTwoCyclicMatchingSourceCell target)).choose 2 +
          (sizeTwoCyclicSelectedOrbitMultiplicity code
            (sizeTwoAllowedDifferenceComplement T)
            (sizeTwoCyclicMatchingSourceCell target)).choose 2 ≠ 6 := by
    intro heq
    exact hunbalanced
      ((sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_eq_six_iff
        code T target).mp heq)
  omega

/-- Across the 48 allowed source-cells, complementary three-fiber halves carry
at least 288 collisions in total.  Equality can only occur when every local
bound above is sharp. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_source_compl_collision_ge_288
    (code : SizeTwoCyclicFullPermutationCode 8 (1 : ZMod 8))
    (T : Finset (sizeTwoAllowedDifference 8 (1 : ZMod 8))) :
    288 ≤ ∑ target : SizeTwoCyclicMatchingSource 8 (1 : ZMod 8),
      ((sizeTwoCyclicSelectedOrbitMultiplicity code T
          (sizeTwoCyclicMatchingSourceCell target)).choose 2 +
        (sizeTwoCyclicSelectedOrbitMultiplicity code
          (sizeTwoAllowedDifferenceComplement T)
          (sizeTwoCyclicMatchingSourceCell target)).choose 2) := by
  calc
    288 = ∑ _target : SizeTwoCyclicMatchingSource 8 (1 : ZMod 8), 6 := by
      rw [Finset.sum_const, Finset.card_univ,
        sizeTwoCyclicMatchingSource_card 8 (1 : ZMod 8) (by decide)]
      norm_num
    _ ≤ _ := Finset.sum_le_sum fun target _ =>
      sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_ge_six
        code T target

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_ge_six
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_eq_six_iff
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_local_compl_collision_ge_seven
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_source_compl_collision_ge_288
