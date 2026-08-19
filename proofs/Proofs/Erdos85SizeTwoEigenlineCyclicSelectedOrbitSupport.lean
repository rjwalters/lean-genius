import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedOrbitReciprocity

/-!
# Support of selected cyclic-orbit multiplicity

Every matching edge has an allowed target difference.  Consequently the
combined multiplicity of any selected source fibers is supported on the
`q(q-2)` allowed source-cells, rather than all `q^2` absolute grid cells.
This sharpens the denominator in the multi-orbit Cauchy lower bound.
-/

namespace Erdos85

noncomputable section

def sizeTwoCyclicSelectedOrbitSupport
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    Finset (SizeTwoCyclicAbsoluteGridEdge q) :=
  Finset.univ.filter fun e =>
    sizeTwoCyclicSelectedOrbitMultiplicity code T e ≠ 0

/-- Every cell with nonzero selected multiplicity is the absolute coordinate
of a unique allowed matching source. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_ne_zero_exists_source
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (e : SizeTwoCyclicAbsoluteGridEdge q)
    (he : sizeTwoCyclicSelectedOrbitMultiplicity code T e ≠ 0) :
    ∃ source : SizeTwoCyclicMatchingSource q a,
      sizeTwoCyclicMatchingSourceCell source = e := by
  classical
  have hpos : 0 < sizeTwoCyclicSelectedOrbitMultiplicity code T e :=
    Nat.pos_of_ne_zero he
  unfold sizeTwoCyclicSelectedOrbitMultiplicity at hpos
  rw [Finset.sum_pos_iff] at hpos
  obtain ⟨t, ht, horbit⟩ := hpos
  unfold sizeTwoCyclicMatchingOrbitMultiplicity at horbit
  obtain ⟨x, hx⟩ := Finset.card_pos.mp horbit
  have hmem := (Finset.mem_filter.mp hx).2
  obtain ⟨s, hs, _⟩ :=
    sizeTwoCyclicSourceMatching_mem_reverse_exists_eq_difference
      code x t e hmem
  refine ⟨(e.1, s), ?_⟩
  apply Prod.ext
  · rfl
  · dsimp [sizeTwoCyclicMatchingSourceCell]
    rw [hs]
    abel

def sizeTwoCyclicSelectedOrbitSupportSource
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (e : {e // e ∈ sizeTwoCyclicSelectedOrbitSupport code T}) :
    SizeTwoCyclicMatchingSource q a :=
  Classical.choose
    (sizeTwoCyclicSelectedOrbitMultiplicity_ne_zero_exists_source
      code T e.1 (Finset.mem_filter.mp e.2).2)

theorem sizeTwoCyclicSelectedOrbitSupportSource_spec
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (e : {e // e ∈ sizeTwoCyclicSelectedOrbitSupport code T}) :
    sizeTwoCyclicMatchingSourceCell
      (sizeTwoCyclicSelectedOrbitSupportSource code T e) = e.1 :=
  Classical.choose_spec
    (sizeTwoCyclicSelectedOrbitMultiplicity_ne_zero_exists_source
      code T e.1 (Finset.mem_filter.mp e.2).2)

theorem sizeTwoCyclicSelectedOrbitSupportSource_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    Function.Injective (sizeTwoCyclicSelectedOrbitSupportSource code T) := by
  intro e f hef
  apply Subtype.ext
  rw [← sizeTwoCyclicSelectedOrbitSupportSource_spec code T e,
    ← sizeTwoCyclicSelectedOrbitSupportSource_spec code T f, hef]

/-- The support has at most `q(q-2)` cells. -/
theorem sizeTwoCyclicSelectedOrbitSupport_card_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (ha : a ≠ -1 - a) :
    (sizeTwoCyclicSelectedOrbitSupport code T).card ≤ q * (q - 2) := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card {e // e ∈ sizeTwoCyclicSelectedOrbitSupport code T} ≤
        Fintype.card (SizeTwoCyclicMatchingSource q a) :=
      Fintype.card_le_of_injective
        (sizeTwoCyclicSelectedOrbitSupportSource code T)
        (sizeTwoCyclicSelectedOrbitSupportSource_injective code T)
    _ = q * (q - 2) := sizeTwoCyclicMatchingSource_card q a ha

/-- Cauchy with the sharp `q(q-2)` support denominator. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_cauchy_allowedSupport
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (ha : a ≠ -1 - a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    (T.card * (q * (q - 2))) ^ 2 ≤
      (q * (q - 2)) *
        ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicSelectedOrbitMultiplicity code T e) ^ 2 := by
  classical
  let M := sizeTwoCyclicSelectedOrbitMultiplicity code T
  let S := sizeTwoCyclicSelectedOrbitSupport code T
  have hsum : (∑ e ∈ S, M e) = ∑ e, M e := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro e heuniv heS
    have hzero : M e = 0 := by
      by_contra hne
      apply heS
      simp [S, sizeTwoCyclicSelectedOrbitSupport, M, hne]
    simp [hzero]
  have hsq : (∑ e ∈ S, (M e) ^ 2) = ∑ e, (M e) ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro e heuniv heS
    have hzero : M e = 0 := by
      by_contra hne
      apply heS
      simp [S, sizeTwoCyclicSelectedOrbitSupport, M, hne]
    simp [hzero]
  have hcauchy := Erdos101OQ02ST.sq_sum_le_card_mul_sum_sq_nat S M
  rw [hsum, hsq,
    sizeTwoCyclicSelectedOrbitMultiplicity_sum code hq1] at hcauchy
  calc
    _ ≤ S.card * ∑ e, (M e) ^ 2 := hcauchy
    _ ≤ (q * (q - 2)) * ∑ e, (M e) ^ 2 :=
      Nat.mul_le_mul_right _
        (sizeTwoCyclicSelectedOrbitSupport_card_le code T ha)

/-- Collision-mass form of the sharp-support Cauchy bound. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_lower_allowedSupport
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (ha : a ≠ -1 - a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    (T.card * (q * (q - 2))) ^ 2 ≤
      (q * (q - 2)) * (T.card * (q * (q - 2)) +
        2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2) := by
  have hcauchy :=
    sizeTwoCyclicSelectedOrbitMultiplicity_cauchy_allowedSupport
      code hq1 ha T
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

/-- Concrete consequence for the minimized q=8 three-fiber core: its
combined collision mass is at least 144. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_ge_144
    (code : SizeTwoCyclicFullPermutationCode 8 (1 : ZMod 8))
    (T : Finset (sizeTwoAllowedDifference 8 (1 : ZMod 8)))
    (hT : T.card = 3) :
    144 ≤ ∑ e : SizeTwoCyclicAbsoluteGridEdge 8,
      (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2 := by
  have h :=
    sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_lower_allowedSupport
      code (by decide) (by decide) T
  norm_num [hT] at h
  omega

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_ne_zero_exists_source
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitSupport_card_le
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_cauchy_allowedSupport
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_lower_allowedSupport
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_ge_144
