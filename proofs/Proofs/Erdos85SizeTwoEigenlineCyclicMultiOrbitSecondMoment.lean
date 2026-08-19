import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingSecondMomentCensus
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingCounts
import Proofs.Erdos101ProblemOQ02

/-!
# Multi-orbit second-moment lower bound

For a selected family of cyclic difference fibers, add their absolute-grid
multiplicities.  The total mass is exact, so Cauchy forces a quantitative
lower bound on the combined collision mass.  This is the algebraic lower
half of the sparse three-fiber packing argument at `q = 8`; reciprocity must
still control how much of this mass can lie between different fibers.
-/

namespace Erdos85

noncomputable section

/-- Total multiplicity of an absolute grid edge across selected difference
fibers. -/
def sizeTwoCyclicSelectedOrbitMultiplicity
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (e : SizeTwoCyclicAbsoluteGridEdge q) : ℕ :=
  ∑ t ∈ T, sizeTwoCyclicMatchingOrbitMultiplicity code t e

/-- One difference fiber has exactly `q(q-2)` incidences with absolute grid
edges. -/
theorem sizeTwoCyclicMatchingOrbitMultiplicity_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (t : sizeTwoAllowedDifference q a) :
    (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      sizeTwoCyclicMatchingOrbitMultiplicity code t e) = q * (q - 2) := by
  classical
  calc
    _ = ∑ e : SizeTwoCyclicAbsoluteGridEdge q, ∑ x : ZMod q,
        if e ∈ sizeTwoCyclicSourceMatching code (x, t) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      unfold sizeTwoCyclicMatchingOrbitMultiplicity
      rw [Finset.card_filter]
    _ = ∑ x : ZMod q, ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        if e ∈ sizeTwoCyclicSourceMatching code (x, t) then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ _x : ZMod q, (q - 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.card_filter]
      simp [sizeTwoCyclicSourceMatching_card_eq_sub_two code hq1]
    _ = q * (q - 2) := by simp [ZMod.card]

/-- Exact total mass across a selected family of difference fibers. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      sizeTwoCyclicSelectedOrbitMultiplicity code T e) =
      T.card * (q * (q - 2)) := by
  classical
  unfold sizeTwoCyclicSelectedOrbitMultiplicity
  rw [Finset.sum_comm]
  simp_rw [sizeTwoCyclicMatchingOrbitMultiplicity_sum code hq1]
  simp

/-- Cauchy's inequality forces the combined multiplicity square-mass to be
large.  The division-free form is convenient for later natural-number
arithmetic. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_cauchy
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    (T.card * (q * (q - 2))) ^ 2 ≤
      q ^ 2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicSelectedOrbitMultiplicity code T e) ^ 2 := by
  have h := Erdos101OQ02ST.sq_sum_le_card_mul_sum_sq_nat
    (Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q))
    (sizeTwoCyclicSelectedOrbitMultiplicity code T)
  rw [sizeTwoCyclicSelectedOrbitMultiplicity_sum code hq1] at h
  have hcard :
      (Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).card = q ^ 2 := by
    simp [Fintype.card_prod, ZMod.card, pow_two]
  rw [hcard] at h
  simpa only [pow_two] using h

/-- Collision-mass form of the multi-orbit Cauchy bound.  It isolates the
sum of `choose 2` multiplicities that the matching-intersection census turns
into within- and cross-fiber agreement mass. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_lower
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    (T.card * (q * (q - 2))) ^ 2 ≤
      q ^ 2 * (T.card * (q * (q - 2)) +
        2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2) := by
  have hcauchy := sizeTwoCyclicSelectedOrbitMultiplicity_cauchy code hq1 T
  have hid :
      (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicSelectedOrbitMultiplicity code T e) ^ 2) =
        (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          sizeTwoCyclicSelectedOrbitMultiplicity code T e) +
        2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    exact Erdos101OQ02ST.sq_eq_self_add_two_mul_choose_two _
  rw [hid, sizeTwoCyclicSelectedOrbitMultiplicity_sum code hq1] at hcauchy
  exact hcauchy

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicMatchingOrbitMultiplicity_sum
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_sum
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_cauchy
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_lower
