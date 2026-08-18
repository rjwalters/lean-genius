import Proofs.Erdos85TaggedFactorization
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Symmetric difference arrays on an odd index set

In the equal-cycle terminal object, every allowed cyclic difference occurs
exactly once in each row of component blocks.  Transposition preserves the
ordered-difference set.  Consequently a fixed difference defines an
involution of the component indices.  On an odd index set it has a fixed
point, so that difference already occurs in a diagonal block.

This keeps the setwise content which is lost in the scalar channel bounds.
-/

namespace Erdos85

noncomputable section

variable {I Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype Z] [DecidableEq Z]

/-- The abstract parity property used by the difference-array argument. -/
def EveryInvolutionHasFixedPoint (I : Type*) : Prop :=
  ∀ f : I → I, Function.Involutive f → ∃ i, f i = i

/-- Every involution of an odd finite type has a fixed point. -/
theorem everyInvolutionHasFixedPoint_of_odd
    (hodd : Odd (Fintype.card I)) : EveryInvolutionHasFixedPoint I := by
  intro f hf
  let σ : Equiv.Perm I :=
    { toFun := f
      invFun := f
      left_inv := hf
      right_inv := hf }
  have hnotdvd : ¬ 2 ∣ Fintype.card I := by
    simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hodd)
  have hpow : σ ^ 2 ^ 1 = 1 := by
    ext i
    simp [σ, pow_two, hf i]
  obtain ⟨i, hi⟩ := Equiv.Perm.exists_fixed_point_of_prime
    (p := 2) (n := 1) hnotdvd hpow
  exact ⟨i, hi⟩

/-- A symmetric array which represents every residue uniquely in every row
has all represented residues on its diagonal, provided involutions of the
index set have fixed points. -/
theorem subset_diagonal_biUnion_of_symmetric_unique_rows
    (R : Finset Z) (D : I → I → Finset Z)
    (hsymm : ∀ i j, D i j = D j i)
    (hrows : ∀ t ∈ R, ∀ i, ∃! j, t ∈ D i j)
    (hfixed : EveryInvolutionHasFixedPoint I) :
    R ⊆ Finset.univ.biUnion (fun i ↦ D i i) := by
  intro t ht
  let f : I → I := fun i ↦ (hrows t ht i).choose
  have hfmem : ∀ i, t ∈ D i (f i) := fun i ↦ (hrows t ht i).choose_spec.1
  have hfinv : Function.Involutive f := by
    intro i
    apply (hrows t ht (f i)).unique
    · exact hfmem (f i)
    · simpa only [hsymm (f i) i] using hfmem i
  obtain ⟨i, hi⟩ := hfixed f hfinv
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  simpa only [hi] using hfmem i

/-- Cardinal form: the allowed difference set is no larger than the total
number of diagonal difference incidences. -/
theorem card_le_sum_diagonal_card_of_symmetric_unique_rows
    (R : Finset Z) (D : I → I → Finset Z)
    (hsymm : ∀ i j, D i j = D j i)
    (hrows : ∀ t ∈ R, ∀ i, ∃! j, t ∈ D i j)
    (hfixed : EveryInvolutionHasFixedPoint I) :
    R.card ≤ ∑ i, (D i i).card := by
  have hsub := subset_diagonal_biUnion_of_symmetric_unique_rows
    R D hsymm hrows hfixed
  calc
    R.card ≤ (Finset.univ.biUnion (fun i ↦ D i i)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i, (D i i).card := Finset.card_biUnion_le

/-- The form used by the equal-cycle terminal object. -/
theorem card_le_sum_diagonal_card_of_symmetric_unique_rows_of_odd
    (R : Finset Z) (D : I → I → Finset Z)
    (hsymm : ∀ i j, D i j = D j i)
    (hrows : ∀ t ∈ R, ∀ i, ∃! j, t ∈ D i j)
    (hodd : Odd (Fintype.card I)) :
    R.card ≤ ∑ i, (D i i).card :=
  card_le_sum_diagonal_card_of_symmetric_unique_rows
    R D hsymm hrows (everyInvolutionHasFixedPoint_of_odd hodd)

/-- A canonical leave and pairwise disjoint block differences say precisely
that each allowed residue occurs in a unique block of the row. -/
theorem existsUnique_mem_orderedDifferenceSet_of_leave
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (A : I → Finset (ZMod r))
    (hleave : unusedOrderedDifferences A = {1, -1})
    (hdisj : ∀ {j k : I}, j ≠ k →
      Disjoint (orderedDifferenceSet (A j))
        (orderedDifferenceSet (A k)))
    {t : ZMod r} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1) :
    ∃! j, t ∈ orderedDifferenceSet (A j) := by
  have htNotUnused : t ∉ unusedOrderedDifferences A := by
    rw [hleave]
    simp [ht1, htm1]
  have htUnion : t ∈ Finset.univ.biUnion
      (fun j ↦ orderedDifferenceSet (A j)) := by
    by_contra ht
    apply htNotUnused
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_erase.mpr ⟨ht0, Finset.mem_univ t⟩, ht⟩
  obtain ⟨j, hjuniv, hj⟩ := Finset.mem_biUnion.mp htUnion
  refine ⟨j, hj, ?_⟩
  intro k hk
  by_contra hjk
  exact Finset.disjoint_left.mp (hdisj hjk) hk hj

/-- The residues available to cycle-block ordered differences at the
second-order boundary. -/
def allowedCycleDifferences (r : ℕ) [NeZero r] : Finset (ZMod r) :=
  Finset.univ \ {0, 1, -1}

theorem card_allowedCycleDifferences
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r) :
    (allowedCycleDifferences r).card = r - 3 := by
  have hone0 : (1 : ZMod r) ≠ 0 := by
    intro h
    have hr1 : r = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  have hminus : (-1 : ZMod r) ≠ 1 := by
    simpa using zmod_sub_one_ne_add_one_of_three_le hr3 (0 : ZMod r)
  have hnegone0 : (-1 : ZMod r) ≠ 0 := neg_ne_zero.mpr hone0
  have hcard : ({0, 1, -1} : Finset (ZMod r)).card = 3 := by
    simp [hone0, hone0.symm, hnegone0, hnegone0.symm,
      hminus, hminus.symm]
  simp only [allowedCycleDifferences]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hcard, ZMod.card]

/-- Terminal abstract difference-array inequality.  If every row is a
canonical cyclic difference packing and block transposition preserves its
ordered differences, then oddness of the component set forces all allowed
differences onto the diagonal. -/
theorem sub_three_le_sum_diagonal_orderedDifference_card
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (A : I → I → Finset (ZMod r))
    (hsymm : ∀ i j,
      orderedDifferenceSet (A i j) = orderedDifferenceSet (A j i))
    (hleave : ∀ i, unusedOrderedDifferences (A i) = {1, -1})
    (hdisj : ∀ i, ∀ {j k : I}, j ≠ k →
      Disjoint (orderedDifferenceSet (A i j))
        (orderedDifferenceSet (A i k)))
    (hodd : Odd (Fintype.card I)) :
    r - 3 ≤ ∑ i, (orderedDifferenceSet (A i i)).card := by
  let D : I → I → Finset (ZMod r) :=
    fun i j ↦ orderedDifferenceSet (A i j)
  have hrows : ∀ t ∈ allowedCycleDifferences r, ∀ i, ∃! j, t ∈ D i j := by
    intro t ht i
    have htdata := Finset.mem_sdiff.mp ht
    have htforbidden := htdata.2
    have ht0 : t ≠ 0 := by
      intro h
      apply htforbidden
      simp [h]
    have ht1 : t ≠ 1 := by
      intro h
      apply htforbidden
      simp [h]
    have htm1 : t ≠ -1 := by
      intro h
      apply htforbidden
      simp [h]
    exact existsUnique_mem_orderedDifferenceSet_of_leave
      hr3 (A i) (hleave i) (hdisj i) ht0 ht1 htm1
  rw [← card_allowedCycleDifferences hr3]
  exact card_le_sum_diagonal_card_of_symmetric_unique_rows_of_odd
    (allowedCycleDifferences r) D hsymm hrows hodd

/-- Immediate numerical terminal form of the difference-array argument. -/
theorem cycleLength_le_degree_add_three_of_symmetric_difference_array
    {r d : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (A : I → I → Finset (ZMod r))
    (hsymm : ∀ i j,
      orderedDifferenceSet (A i j) = orderedDifferenceSet (A j i))
    (hleave : ∀ i, unusedOrderedDifferences (A i) = {1, -1})
    (hdisj : ∀ i, ∀ {j k : I}, j ≠ k →
      Disjoint (orderedDifferenceSet (A i j))
        (orderedDifferenceSet (A i k)))
    (hodd : Odd (Fintype.card I))
    (hdiag : ∑ i, (orderedDifferenceSet (A i i)).card ≤ d) :
    r ≤ d + 3 := by
  have harray := sub_three_le_sum_diagonal_orderedDifference_card
    hr3 A hsymm hleave hdisj hodd
  omega

/-- Quotient form of the diagonal-mass calculation.  If diagonal block
degrees are even and at most two, their Sidon difference mass equals their
degree; the quotient trace therefore supplies the exact total. -/
theorem sum_diagonal_orderedDifference_card_eq_of_trace
    [AddCommGroup Z]
    (A : I → Finset Z) (q : I → ℕ) {d : ℕ}
    (hcard : ∀ i, (A i).card = q i)
    (hsidon : ∀ i, IsOrderedSidon (A i))
    (heven : ∀ i, Even (q i))
    (hle : ∀ i, q i ≤ 2)
    (htrace : ∑ i, q i = d) :
    ∑ i, (orderedDifferenceSet (A i)).card = d := by
  calc
    ∑ i, (orderedDifferenceSet (A i)).card =
        ∑ i, q i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [card_orderedDifferenceSet_of_sidon (hsidon i), hcard i]
      have hcases : q i = 0 ∨ q i = 2 := by
        obtain ⟨k, hk⟩ := heven i
        have hlei := hle i
        omega
      rcases hcases with hzero | htwo
      · simp [hzero]
      · simp [htwo]
    _ = d := htrace

end

end Erdos85
