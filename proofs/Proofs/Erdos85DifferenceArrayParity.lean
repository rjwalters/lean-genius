import Proofs.Erdos85GraphDiagonalAnchor

/-!
# Parity refinement of the odd difference-array argument

Existence of a diagonal occurrence is only the first consequence of the
row involution.  The non-fixed indices occur in pairs, so on an odd index
set the number of diagonal occurrences of every represented residue is odd.
This remains true when there is diagonal surplus.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

variable {I Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype Z] [DecidableEq Z]

theorem odd_card_fixedPoints_of_involution
    (f : I → I) (hf : Function.Involutive f)
    (hodd : Odd (Fintype.card I)) :
    Odd ((Finset.univ.filter fun i ↦ f i = i).card) := by
  let fixed : Finset I := Finset.univ.filter fun i ↦ f i = i
  let moved : Finset I := Finset.univ.filter fun i ↦ f i ≠ i
  have hsum : ∑ _i ∈ moved, (1 : ZMod 2) = 0 := by
    apply Finset.sum_involution (fun i _ ↦ f i)
    · intro i hi
      change (1 : ZMod 2) + 1 = 0
      decide
    · intro i hi _
      exact (Finset.mem_filter.mp hi).2
    · intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hfix
      have := congrArg f hfix
      rw [hf i] at this
      exact (Finset.mem_filter.mp hi).2 this
    · intro i _
      exact hf i
  have hmovedEven : Even moved.card := by
    rw [← ZMod.natCast_eq_zero_iff_even]
    simpa using hsum
  have hdisj : Disjoint fixed moved := by
    apply Finset.disjoint_left.mpr
    intro i hfi hmi
    exact (Finset.mem_filter.mp hmi).2 (Finset.mem_filter.mp hfi).2
  have hunion : fixed ∪ moved = Finset.univ := by
    ext i
    by_cases hi : f i = i <;> simp [fixed, moved, hi]
  have hparts : fixed.card + moved.card = Fintype.card I := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hsumOdd : Odd (fixed.card + moved.card) := by
    rw [hparts]
    exact hodd
  have hfixedOdd : Odd fixed.card := by
    exact (Nat.odd_add.mp hsumOdd).mpr hmovedEven
  exact hfixedOdd

/-- Parity refinement of `subset_diagonal_biUnion...`: every represented
residue occurs in an odd number of diagonal blocks. -/
theorem odd_card_diagonal_occurrences_of_symmetric_unique_rows
    (R : Finset Z) (D : I → I → Finset Z)
    (hsymm : ∀ i j, D i j = D j i)
    (hrows : ∀ t ∈ R, ∀ i, ∃! j, t ∈ D i j)
    (hodd : Odd (Fintype.card I))
    (t : Z) (ht : t ∈ R) :
    Odd ((Finset.univ.filter fun i ↦ t ∈ D i i).card) := by
  let f : I → I := fun i ↦ (hrows t ht i).choose
  have hfmem : ∀ i, t ∈ D i (f i) :=
    fun i ↦ (hrows t ht i).choose_spec.1
  have hfinv : Function.Involutive f := by
    intro i
    apply (hrows t ht (f i)).unique
    · exact hfmem (f i)
    · simpa only [hsymm (f i) i] using hfmem i
  have hfixed := odd_card_fixedPoints_of_involution f hfinv hodd
  have heq : (Finset.univ.filter fun i ↦ f i = i) =
      Finset.univ.filter fun i ↦ t ∈ D i i := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      simpa [hi] using hfmem i
    · intro hi
      exact ((hrows t ht i).unique hi (hfmem i)).symm
  rw [heq] at hfixed
  exact hfixed

/-- Canonical cyclic form: every allowed difference has odd diagonal
multiplicity. -/
theorem odd_card_diagonal_orderedDifference_occurrences
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (A : I → I → Finset (ZMod r))
    (hsymm : ∀ i j,
      orderedDifferenceSet (A i j) = orderedDifferenceSet (A j i))
    (hleave : ∀ i, unusedOrderedDifferences (A i) = {1, -1})
    (hdisj : ∀ i, ∀ {j k : I}, j ≠ k →
      Disjoint (orderedDifferenceSet (A i j))
        (orderedDifferenceSet (A i k)))
    (hodd : Odd (Fintype.card I))
    (t : ZMod r) (ht : t ∈ allowedCycleDifferences r) :
    Odd ((Finset.univ.filter fun i ↦
      t ∈ orderedDifferenceSet (A i i)).card) := by
  let D : I → I → Finset (ZMod r) :=
    fun i j ↦ orderedDifferenceSet (A i j)
  have hrows : ∀ s ∈ allowedCycleDifferences r, ∀ i,
      ∃! j, s ∈ D i j := by
    intro s hs i
    have hsNot := (Finset.mem_sdiff.mp hs).2
    have hs0 : s ≠ 0 := fun h ↦ hsNot (by simp [h])
    have hs1 : s ≠ 1 := fun h ↦ hsNot (by simp [h])
    have hsm1 : s ≠ -1 := fun h ↦ hsNot (by simp [h])
    exact existsUnique_mem_orderedDifferenceSet_of_leave
      hr3 (A i) (hleave i) (hdisj i) hs0 hs1 hsm1
  exact odd_card_diagonal_occurrences_of_symmetric_unique_rows
    (allowedCycleDifferences r) D hsymm hrows hodd t ht

/-- Iff form: forbidden differences have no occurrence at all, while every
allowed difference has odd diagonal multiplicity. -/
theorem odd_card_diagonal_orderedDifference_occurrences_iff
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (A : I → I → Finset (ZMod r))
    (hsymm : ∀ i j,
      orderedDifferenceSet (A i j) = orderedDifferenceSet (A j i))
    (hleave : ∀ i, unusedOrderedDifferences (A i) = {1, -1})
    (hdisj : ∀ i, ∀ {j k : I}, j ≠ k →
      Disjoint (orderedDifferenceSet (A i j))
        (orderedDifferenceSet (A i k)))
    (hodd : Odd (Fintype.card I)) (t : ZMod r) :
    Odd ((Finset.univ.filter fun i ↦
      t ∈ orderedDifferenceSet (A i i)).card) ↔
      t ∈ allowedCycleDifferences r := by
  constructor
  · intro ho
    have hne : (Finset.univ.filter fun i ↦
        t ∈ orderedDifferenceSet (A i i)).card ≠ 0 := by
      intro hz
      rw [hz] at ho
      exact Nat.not_odd_zero ho
    have hpos : 0 < (Finset.univ.filter fun i ↦
        t ∈ orderedDifferenceSet (A i i)).card := Nat.pos_of_ne_zero hne
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    have hti : t ∈ orderedDifferenceSet (A i i) :=
      (Finset.mem_filter.mp hi).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ t, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro ht0
      exact zero_not_mem_orderedDifferenceSet (A i i) (ht0 ▸ hti)
    · intro ht1
      have hu : (1 : ZMod r) ∈ unusedOrderedDifferences (A i) := by
        rw [hleave i]
        simp
      rw [unusedOrderedDifferences] at hu
      exact (Finset.mem_sdiff.mp hu).2
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ht1 ▸ hti⟩)
    · intro htm1
      have hu : (-1 : ZMod r) ∈ unusedOrderedDifferences (A i) := by
        rw [hleave i]
        simp
      rw [unusedOrderedDifferences] at hu
      exact (Finset.mem_sdiff.mp hu).2
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, htm1 ▸ hti⟩)
  · exact odd_card_diagonal_orderedDifference_occurrences
      hr3 A hsymm hleave hdisj hodd t

end

end Erdos85
