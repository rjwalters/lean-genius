import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingReciprocity
import Proofs.Erdos85SizeTwoEigenlineCyclicMultiOrbitSecondMoment

/-!
# Reciprocity for selected cyclic difference fibers

The combined multiplicity of selected source fibers at a target source-cell
can be read in the reverse direction: it is exactly the number of selected
source-cells in that target's own matching.  This pointwise conservation law
is the interface between the multi-orbit Cauchy lower bound and the remaining
cross-fiber estimate.
-/

namespace Erdos85

noncomputable section

/-- Pointwise selected-fiber incidence is invariant under reversing every
matching edge. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (target : SizeTwoCyclicMatchingSource q a) :
    sizeTwoCyclicSelectedOrbitMultiplicity code T
        (sizeTwoCyclicMatchingSourceCell target) =
      ∑ t ∈ T, ((Finset.univ : Finset (ZMod q)).filter fun x =>
        sizeTwoCyclicMatchingSourceCell (x, t) ∈
          sizeTwoCyclicSourceMatching code target).card := by
  classical
  unfold sizeTwoCyclicSelectedOrbitMultiplicity
  apply Finset.sum_congr rfl
  intro t ht
  unfold sizeTwoCyclicMatchingOrbitMultiplicity
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact sizeTwoCyclicSourceMatching_sourceCell_mem_comm
    code (x, t) target

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell
