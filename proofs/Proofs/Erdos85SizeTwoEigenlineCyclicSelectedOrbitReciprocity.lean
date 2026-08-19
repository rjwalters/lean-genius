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

/-- Selected-fiber multiplicity at a source-cell is bounded by the size of
that cell's full matching: reversal injects every selected incident source
into a distinct matching edge. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_le_matchingCard
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (target : SizeTwoCyclicMatchingSource q a) :
    sizeTwoCyclicSelectedOrbitMultiplicity code T
        (sizeTwoCyclicMatchingSourceCell target) ≤
      (sizeTwoCyclicSourceMatching code target).card := by
  classical
  let W := Σ t : {t // t ∈ T},
    {x : ZMod q // sizeTwoCyclicMatchingSourceCell (x, t.1) ∈
      sizeTwoCyclicSourceMatching code target}
  let f : W → {e // e ∈ sizeTwoCyclicSourceMatching code target} :=
    fun w ↦ ⟨sizeTwoCyclicMatchingSourceCell (w.2.1, w.1.1), w.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨t, x⟩ ⟨u, y⟩ h
    have hcell := congrArg Subtype.val h
    have hsource := sizeTwoCyclicMatchingSourceCell_injective hcell
    have htu : t = u := Subtype.ext (congrArg Prod.snd hsource)
    subst u
    have hxy : x = y := Subtype.ext (congrArg Prod.fst hsource)
    subst y
    rfl
  rw [sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell code T target]
  calc
    (∑ t ∈ T, ((Finset.univ : Finset (ZMod q)).filter fun x =>
        sizeTwoCyclicMatchingSourceCell (x, t) ∈
          sizeTwoCyclicSourceMatching code target).card) = Fintype.card W := by
      rw [show Fintype.card W =
          ∑ t : {t // t ∈ T}, Fintype.card
            {x : ZMod q // sizeTwoCyclicMatchingSourceCell (x, t.1) ∈
              sizeTwoCyclicSourceMatching code target} by
        simp [W, Fintype.card_sigma]]
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Fintype.card_subtype]
    _ ≤ Fintype.card {e // e ∈ sizeTwoCyclicSourceMatching code target} :=
      Fintype.card_le_of_injective f hf
    _ = (sizeTwoCyclicSourceMatching code target).card := Fintype.card_coe _

/-- Numerical pointwise cap supplied by reciprocity. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_le_sub_two
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (T : Finset (sizeTwoAllowedDifference q a))
    (target : SizeTwoCyclicMatchingSource q a) :
    sizeTwoCyclicSelectedOrbitMultiplicity code T
        (sizeTwoCyclicMatchingSourceCell target) ≤ q - 2 := by
  calc
    _ ≤ (sizeTwoCyclicSourceMatching code target).card :=
      sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_le_matchingCard
        code T target
    _ = q - 2 := sizeTwoCyclicSourceMatching_card_eq_sub_two
      code hq1 target

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_le_matchingCard
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell_le_sub_two
