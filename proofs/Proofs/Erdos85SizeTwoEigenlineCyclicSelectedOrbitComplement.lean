import Proofs.Erdos85SizeTwoEigenlineCyclicFullOrbitRegularity
import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedOrbitSupport

/-!
# Complementary selected cyclic fibers

Full-fiber reciprocity regularity splits exactly across a selected family and
its complement.  In the q=8 three-fiber core, both halves therefore carry
the same sharp-support collision pressure.
-/

namespace Erdos85

noncomputable section

/-- The fibers not selected by `T`.  Naming this operation avoids exposing a
decidable-equality choice in theorem statements. -/
def sizeTwoAllowedDifferenceComplement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (T : Finset (sizeTwoAllowedDifference q a)) :
    Finset (sizeTwoAllowedDifference q a) := by
  classical
  exact Finset.univ \ T

/-- Selected and complementary multiplicities partition full-orbit
multiplicity at every absolute cell. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_add_compl
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (e : SizeTwoCyclicAbsoluteGridEdge q) :
    sizeTwoCyclicSelectedOrbitMultiplicity code T e +
      sizeTwoCyclicSelectedOrbitMultiplicity code
        (sizeTwoAllowedDifferenceComplement T) e =
      sizeTwoCyclicSelectedOrbitMultiplicity code Finset.univ e := by
  classical
  unfold sizeTwoAllowedDifferenceComplement
  unfold sizeTwoCyclicSelectedOrbitMultiplicity
  rw [← Finset.sum_union Finset.disjoint_sdiff]
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ T)]

/-- On every allowed source-cell, selected and complementary multiplicities
sum to the exact full degree `q-2`. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_add_compl
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (T : Finset (sizeTwoAllowedDifference q a))
    (target : SizeTwoCyclicMatchingSource q a) :
    sizeTwoCyclicSelectedOrbitMultiplicity code T
      (sizeTwoCyclicMatchingSourceCell target) +
      sizeTwoCyclicSelectedOrbitMultiplicity code
        (sizeTwoAllowedDifferenceComplement T)
        (sizeTwoCyclicMatchingSourceCell target) = q - 2 := by
  rw [sizeTwoCyclicSelectedOrbitMultiplicity_add_compl]
  exact sizeTwoCyclicFullOrbitMultiplicity_sourceCell_eq_sub_two
    code hq1 target

/-- In the q=8, a=1 code the complement of a three-fiber selection also has
three fibers. -/
theorem sizeTwoCyclicAllowedDifference_compl_card_eq_three_eight
    (T : Finset (sizeTwoAllowedDifference 8 (1 : ZMod 8)))
    (hT : T.card = 3) :
    (sizeTwoAllowedDifferenceComplement T).card = 3 := by
  classical
  unfold sizeTwoAllowedDifferenceComplement
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ T),
    Finset.card_univ, sizeTwoAllowedDifference_card 8 (1 : ZMod 8) (by decide), hT]

/-- The complementary three fibers obey the same collision lower bound 144. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_compl_choose_two_sum_ge_144
    (code : SizeTwoCyclicFullPermutationCode 8 (1 : ZMod 8))
    (T : Finset (sizeTwoAllowedDifference 8 (1 : ZMod 8)))
    (hT : T.card = 3) :
    144 ≤ ∑ e : SizeTwoCyclicAbsoluteGridEdge 8,
      (sizeTwoCyclicSelectedOrbitMultiplicity code
        (sizeTwoAllowedDifferenceComplement T) e).choose 2 :=
  sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_ge_144 code
    (sizeTwoAllowedDifferenceComplement T)
    (sizeTwoCyclicAllowedDifference_compl_card_eq_three_eight T hT)

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_add_compl
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_add_compl
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_compl_choose_two_sum_ge_144
