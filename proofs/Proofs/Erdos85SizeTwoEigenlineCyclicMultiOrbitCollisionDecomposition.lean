import Proofs.Erdos85SizeTwoEigenlineCyclicMultiOrbitSecondMoment
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingReciprocity
import Mathlib.Data.Finset.Prod

/-!
# Within- and cross-fiber collision decomposition

The selected-orbit second moment splits into within-fiber cherries and an
ordered cross-fiber product.  The factor two on the choose terms makes the
formula division-free and avoids choosing orientations of unordered pairs.
-/

namespace Erdos85

noncomputable section

/-- Elementary square/choose identity used by the collision decomposition. -/
theorem two_mul_choose_two_add_self (n : ℕ) :
    2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
        rw [Nat.choose_succ_succ']
        simp [Nat.choose_one_right, Nat.add_comm]
      rw [hchoose]
      nlinarith

theorem two_mul_choose_two_add (m n : ℕ) :
    2 * (m + n).choose 2 =
      2 * m.choose 2 + 2 * n.choose 2 + 2 * (m * n) := by
  have hm := two_mul_choose_two_add_self m
  have hn := two_mul_choose_two_add_self n
  have hmn := two_mul_choose_two_add_self (m + n)
  nlinarith

/-- Generic ordered cross-term expansion for the choose-two of a finite sum. -/
theorem two_mul_choose_two_sum_eq_sum_within_add_sum_offDiag
    {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ℕ) :
    2 * (∑ t ∈ T, f t).choose 2 =
      (∑ t ∈ T, 2 * (f t).choose 2) +
        ∑ p ∈ T.offDiag, f p.1 * f p.2 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [Finset.sum_insert ha, two_mul_choose_two_add, ih]
      rw [Finset.offDiag_insert ha]
      have hleft : Disjoint T.offDiag ({a} ×ˢ T) := by
        rw [Finset.disjoint_left]
        intro p hp hnew
        simp only [Finset.mem_offDiag] at hp
        simp only [Finset.mem_product, Finset.mem_singleton] at hnew
        exact ha (hnew.1 ▸ hp.1)
      have hcross : Disjoint ({a} ×ˢ T) (T ×ˢ {a}) := by
        rw [Finset.disjoint_left]
        intro p hforward hreverse
        simp only [Finset.mem_product, Finset.mem_singleton] at hforward hreverse
        exact ha (hforward.1 ▸ hreverse.1)
      have hright : Disjoint (T.offDiag ∪ {a} ×ˢ T) (T ×ˢ {a}) := by
        rw [Finset.disjoint_left]
        intro p hleft' hreverse
        simp only [Finset.mem_union] at hleft'
        rcases hleft' with hdiag | hforward
        · simp only [Finset.mem_offDiag] at hdiag
          simp only [Finset.mem_product, Finset.mem_singleton] at hreverse
          exact ha (hreverse.2 ▸ hdiag.2.1)
        · exact Finset.disjoint_left.mp hcross hforward hreverse
      rw [Finset.sum_union hright, Finset.sum_union hleft]
      simp [ha]
      rw [Finset.mul_sum]
      ring

/-- Pointwise split of the selected orbit collision multiplicity. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_decomposition
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (e : SizeTwoCyclicAbsoluteGridEdge q) :
    2 * (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2 =
      (∑ t ∈ T,
        2 * (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) +
      ∑ p ∈ T.offDiag,
        sizeTwoCyclicMatchingOrbitMultiplicity code p.1 e *
          sizeTwoCyclicMatchingOrbitMultiplicity code p.2 e := by
  classical
  unfold sizeTwoCyclicSelectedOrbitMultiplicity
  exact two_mul_choose_two_sum_eq_sum_within_add_sum_offDiag T
    (fun t => sizeTwoCyclicMatchingOrbitMultiplicity code t e)

/-- Summed split: the selected collision mass is the sum of all within-fiber
agreement mass plus the ordered cross-fiber overlap mass. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_decomposition
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2 =
      (∑ t ∈ T, 2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) +
      ∑ p ∈ T.offDiag, ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        sizeTwoCyclicMatchingOrbitMultiplicity code p.1 e *
          sizeTwoCyclicMatchingOrbitMultiplicity code p.2 e := by
  classical
  rw [Finset.mul_sum]
  simp_rw [sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_decomposition
    code T]
  rw [Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.sum_comm]
  · simp_rw [← Finset.mul_sum]

end

end Erdos85

#print axioms Erdos85.two_mul_choose_two_sum_eq_sum_within_add_sum_offDiag
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_decomposition
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_decomposition
