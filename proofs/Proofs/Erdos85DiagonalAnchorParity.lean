import Proofs.Erdos85DifferenceArrayEquality

/-!
# Parity of diagonal-anchor multiplicities

An exact one-fold cover by diagonal difference sets immediately determines
the multiplicity of an anchor coordinate, once membership of the anchor is
identified with membership of its doubled ordered difference.
-/

namespace Erdos85

noncomputable section

variable {I Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype Z] [DecidableEq Z]

def anchorMultiplicity (A : I → Finset Z) (h : Z) : ℕ :=
  (Finset.univ.filter fun i ↦ h ∈ A i).card

/-- An inverse-closed family has an even Fourier weight: its anchor
multiplicity is unchanged by negating the cyclic coordinate. -/
theorem anchorMultiplicity_neg_eq
    {Z : Type*} [AddCommGroup Z] [Fintype Z] [DecidableEq Z]
    (A : I → Finset Z) (hneg : ∀ i, negFinset (A i) = A i) (h : Z) :
    anchorMultiplicity A (-h) = anchorMultiplicity A h := by
  unfold anchorMultiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hh
    rw [← hneg i]
    exact (mem_negFinset_iff (A i) h).mpr hh
  · intro hh
    rw [← hneg i]
    exact (mem_negFinset_iff (A i) (-h)).mpr (by simpa using hh)

/-- Exact difference coverage makes the anchor multiplicity the indicator of
the allowed doubled difference. -/
theorem anchorMultiplicity_eq_one_iff
    (R : Finset Z) (A D : I → Finset Z) (double : Z → Z)
    (hmem : ∀ h i, h ∈ A i ↔ double h ∈ D i)
    (hcontained : ∀ i, D i ⊆ R)
    (hexact : ∀ t ∈ R, ∃! i, t ∈ D i) (h : Z) :
    anchorMultiplicity A h = if double h ∈ R then 1 else 0 := by
  unfold anchorMultiplicity
  split_ifs with hR
  · obtain ⟨i, hi, huniq⟩ := hexact (double h) hR
    have hfilter :
        Finset.univ.filter (fun j ↦ h ∈ A j) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [hmem]
      constructor
      · exact huniq j
      · intro hj
        simpa [hj] using hi
    rw [hfilter]
    simp
  · have hfilter :
        Finset.univ.filter (fun i ↦ h ∈ A i) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      rw [hmem]
      intro hi
      exact hR (hcontained i hi)
    rw [hfilter]
    simp

theorem odd_anchorMultiplicity_iff
    (R : Finset Z) (A D : I → Finset Z) (double : Z → Z)
    (hmem : ∀ h i, h ∈ A i ↔ double h ∈ D i)
    (hcontained : ∀ i, D i ⊆ R)
    (hexact : ∀ t ∈ R, ∃! i, t ∈ D i) (h : Z) :
    Odd (anchorMultiplicity A h) ↔ double h ∈ R := by
  rw [anchorMultiplicity_eq_one_iff R A D double hmem hcontained hexact h]
  split_ifs <;> simp_all

/-- For a loopless inverse-closed support of size at most two on an odd
cycle, membership of `h` is equivalent to occurrence of the ordered
difference `2h`. -/
theorem mem_iff_two_mul_mem_orderedDifferenceSet_of_inverse_pair
    {r : ℕ} [NeZero r] (hrOdd : Odd r)
    (A : Finset (ZMod r))
    (hneg : negFinset A = A) (hcard : A.card ≤ 2)
    (hzero : (0 : ZMod r) ∉ A) (h : ZMod r) :
    h ∈ A ↔ 2 * h ∈ orderedDifferenceSet A := by
  have htwoUnit : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
      (Nat.coprime_two_left.mpr hrOdd)
  have hnegMem (x : ZMod r) (hx : x ∈ A) : -x ∈ A := by
    rw [← hneg]
    exact (mem_negFinset_iff A (-x)).mpr (by simpa using hx)
  constructor
  · intro hh
    have hnh : h ≠ -h := by
      intro heq
      have hz2 : 2 * h = 0 := by
        calc
          2 * h = h + h := two_mul h
          _ = h + (-h) := congrArg (h + ·) heq
          _ = 0 := add_neg_cancel h
      have hz : h = 0 := htwoUnit.mul_right_injective (by simpa using hz2)
      exact hzero (hz ▸ hh)
    simp only [orderedDifferenceSet, Finset.mem_image]
    refine ⟨(h, -h), mem_orderedDistinctPairs_iff.mpr
      ⟨hh, hnegMem h hh, hnh⟩, ?_⟩
    ring
  · intro hd
    simp only [orderedDifferenceSet, Finset.mem_image] at hd
    obtain ⟨⟨x, y⟩, hxyMem, hdiff⟩ := hd
    obtain ⟨hx, hy, hxy⟩ := mem_orderedDistinctPairs_iff.mp hxyMem
    have hpairSub : ({x, y} : Finset (ZMod r)) ⊆ A := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have hpairCard : ({x, y} : Finset (ZMod r)).card = 2 := by
      simp [hxy]
    have hAcard : A.card = 2 := by
      have := Finset.card_le_card hpairSub
      omega
    have hAeq : A = {x, y} := by
      symm
      apply Finset.eq_of_subset_of_card_le hpairSub
      rw [hAcard, hpairCard]
    have hxneg : x ≠ -x := by
      intro heq
      have hz2 : 2 * x = 0 := by
        calc
          2 * x = x + x := two_mul x
          _ = x + (-x) := congrArg (x + ·) heq
          _ = 0 := add_neg_cancel x
      have hz : x = 0 := htwoUnit.mul_right_injective (by simpa using hz2)
      exact hzero (hz ▸ hx)
    have hyneg : y = -x := by
      have hm := hnegMem x hx
      rw [hAeq] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact False.elim (hxneg hm.symm)
      · exact hm.symm
    have htwoEq : 2 * x = 2 * h := by
      rw [hyneg] at hdiff
      simpa [two_mul] using hdiff
    have hxh : x = h := htwoUnit.mul_right_injective htwoEq
    exact hxh ▸ hx

end

end Erdos85
