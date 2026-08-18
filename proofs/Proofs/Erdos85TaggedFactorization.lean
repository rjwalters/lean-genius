import Proofs.Erdos85DifferencePacking

/-!
# Tagged cyclic factorizations from off-diagonal blocks

After orienting a fixed source--target pair, the off-diagonal square identity
says that the products through all intermediate components partition the
cyclic coordinate group, with a unique tagged representation.  This file
records that additive object independently of graph bookkeeping.
-/

namespace Erdos85

noncomputable section

variable {Z K : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
  [Fintype K] [DecidableEq K]

/-- A pair chosen in one tagged channel. -/
abbrev TaggedPair (A B : K → Finset Z) :=
  Σ k : K, (↑(A k) × ↑(B k))

def taggedPairSum {A B : K → Finset Z} (p : TaggedPair A B) : Z :=
  (p.2.1.1 : Z) + p.2.2.1

/-- Every group element has exactly one representation, including the tag of
the intermediate channel. -/
def HasUniqueTaggedSums (A B : K → Finset Z) : Prop :=
  ∀ t : Z, ∃! p : TaggedPair A B, taggedPairSum p = t

theorem taggedPairSum_bijective {A B : K → Finset Z}
    (h : HasUniqueTaggedSums A B) :
    Function.Bijective (taggedPairSum : TaggedPair A B → Z) := by
  constructor
  · intro p q hpq
    exact (h (taggedPairSum p)).unique rfl hpq.symm
  · intro t
    obtain ⟨p, hp, huniq⟩ := h t
    exact ⟨p, hp⟩

/-- Counting the tagged bijection gives the off-diagonal quotient equation
`sum_k |A_k||B_k|=|Z|`. -/
theorem sum_card_mul_card_eq_of_uniqueTaggedSums
    {A B : K → Finset Z} (h : HasUniqueTaggedSums A B) :
    (∑ k, (A k).card * (B k).card) = Fintype.card Z := by
  let e : TaggedPair A B ≃ Z :=
    Equiv.ofBijective taggedPairSum (taggedPairSum_bijective h)
  have hc := Fintype.card_congr e
  simpa only [TaggedPair, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_coe] using hc

/-- Within each active channel, tagged uniqueness separates the two ordered
difference sets. -/
theorem orderedDifferenceSet_disjoint_of_uniqueTaggedSums
    {A B : K → Finset Z} (h : HasUniqueTaggedSums A B) (k : K) :
    Disjoint (orderedDifferenceSet (A k))
      (orderedDifferenceSet (B k)) := by
  apply orderedDifferenceSet_disjoint_of_unique_add
  intro a₁ ha₁ b₂ hb₂ a₂ ha₂ b₁ hb₁ hsum
  let p : TaggedPair A B :=
    ⟨k, ⟨⟨a₁, ha₁⟩, ⟨b₂, hb₂⟩⟩⟩
  let q : TaggedPair A B :=
    ⟨k, ⟨⟨a₂, ha₂⟩, ⟨b₁, hb₁⟩⟩⟩
  have hp : taggedPairSum p = a₁ + b₂ := by rfl
  have hq : taggedPairSum q = a₁ + b₂ := by
    simpa [q, taggedPairSum] using hsum.symm
  have hpq : p = q := (h (a₁ + b₂)).unique hp hq
  have hpair : (⟨⟨a₁, ha₁⟩, ⟨b₂, hb₂⟩⟩ :
      ↑(A k) × ↑(B k)) = ⟨⟨a₂, ha₂⟩, ⟨b₁, hb₁⟩⟩ := by
    change (⟨k, ⟨⟨a₁, ha₁⟩, ⟨b₂, hb₂⟩⟩⟩ : TaggedPair A B) =
      ⟨k, ⟨⟨a₂, ha₂⟩, ⟨b₁, hb₁⟩⟩⟩ at hpq
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hpq
  exact ⟨
    congrArg (fun x ↦ (x.1.1 : Z)) hpair,
    congrArg (fun x ↦ (x.2.1 : Z)) hpair⟩

/-- Each individual channel sum map is injective. -/
theorem channel_add_injective_of_uniqueTaggedSums
    {A B : K → Finset Z} (h : HasUniqueTaggedSums A B) (k : K) :
    Function.Injective (fun p : ↑(A k) × ↑(B k) ↦
      (p.1.1 : Z) + p.2.1) := by
  intro p q hpq
  let p' : TaggedPair A B := ⟨k, p⟩
  let q' : TaggedPair A B := ⟨k, q⟩
  have hp'q' : p' = q' := (h ((p.1.1 : Z) + p.2.1)).unique rfl (by
    simpa [p', q', taggedPairSum] using hpq.symm)
  change (⟨k, p⟩ : TaggedPair A B) = ⟨k, q⟩ at hp'q'
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hp'q'

/-- Sums produced by two different tags are disjoint. -/
theorem channel_sums_ne_of_uniqueTaggedSums
    {A B : K → Finset Z} (h : HasUniqueTaggedSums A B)
    {k l : K} (hkl : k ≠ l)
    (a : ↑(A k)) (b : ↑(B k)) (c : ↑(A l)) (d : ↑(B l)) :
    (a.1 : Z) + b.1 ≠ c.1 + d.1 := by
  intro heq
  let p : TaggedPair A B := ⟨k, ⟨a, b⟩⟩
  let q : TaggedPair A B := ⟨l, ⟨c, d⟩⟩
  have hpq : p = q := (h ((a.1 : Z) + b.1)).unique rfl (by
    simpa [p, q, taggedPairSum] using heq.symm)
  exact hkl (congrArg Sigma.fst hpq)

/-- If both row families have the canonical cycle leave `{1,-1}`, then in
each tagged channel the two (already disjoint) difference sets together use
at most the `r-3` allowed residues. -/
theorem channel_difference_card_sum_le_sub_three
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    {A B : K → Finset (ZMod r)} (h : HasUniqueTaggedSums A B)
    (hAleave : unusedOrderedDifferences A = {1, -1})
    (hBleave : unusedOrderedDifferences B = {1, -1})
    (k : K) :
    (orderedDifferenceSet (A k)).card +
      (orderedDifferenceSet (B k)).card ≤ r - 3 := by
  let forbidden : Finset (ZMod r) := {0, 1, -1}
  have hone0 : (1 : ZMod r) ≠ 0 := by
    intro hzero
    have hr1 : r = 1 := ZMod.one_eq_zero_iff.mp hzero
    omega
  have hminus : (-1 : ZMod r) ≠ 1 := by
    simpa using zmod_sub_one_ne_add_one_of_three_le hr3 (0 : ZMod r)
  have hnegone0 : (-1 : ZMod r) ≠ 0 := neg_ne_zero.mpr hone0
  have hforbidden : forbidden.card = 3 := by
    simp [forbidden, hone0, hone0.symm, hnegone0, hnegone0.symm,
      hminus, hminus.symm]
  have hsubA : orderedDifferenceSet (A k) ⊆ Finset.univ \ forbidden := by
    intro z hz
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ z, ?_⟩
    intro hzforbid
    simp only [forbidden, Finset.mem_insert, Finset.mem_singleton] at hzforbid
    rcases hzforbid with rfl | rfl | rfl
    · exact zero_not_mem_orderedDifferenceSet (A k) hz
    · have hu : (1 : ZMod r) ∈ unusedOrderedDifferences A := by
        rw [hAleave]
        simp
      have hnotUnion := (Finset.mem_sdiff.mp hu).2
      apply hnotUnion
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hz⟩
    · have hu : (-1 : ZMod r) ∈ unusedOrderedDifferences A := by
        rw [hAleave]
        simp
      have hnotUnion := (Finset.mem_sdiff.mp hu).2
      apply hnotUnion
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hz⟩
  have hsubB : orderedDifferenceSet (B k) ⊆ Finset.univ \ forbidden := by
    intro z hz
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ z, ?_⟩
    intro hzforbid
    simp only [forbidden, Finset.mem_insert, Finset.mem_singleton] at hzforbid
    rcases hzforbid with rfl | rfl | rfl
    · exact zero_not_mem_orderedDifferenceSet (B k) hz
    · have hu : (1 : ZMod r) ∈ unusedOrderedDifferences B := by
        rw [hBleave]
        simp
      exact (Finset.mem_sdiff.mp hu).2
        (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hz⟩)
    · have hu : (-1 : ZMod r) ∈ unusedOrderedDifferences B := by
        rw [hBleave]
        simp
      exact (Finset.mem_sdiff.mp hu).2
        (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hz⟩)
  have hdisj := orderedDifferenceSet_disjoint_of_uniqueTaggedSums h k
  have hunion : orderedDifferenceSet (A k) ∪ orderedDifferenceSet (B k) ⊆
      Finset.univ \ forbidden := Finset.union_subset hsubA hsubB
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_sdiff_of_subset (Finset.subset_univ forbidden),
    Finset.card_univ, hforbidden] at hcard
  simpa using hcard

/-- Sidonicity converts the preceding support bound to the quadratic channel
inequality used by the component quotient. -/
theorem channel_card_mul_pred_sum_le_sub_three
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    {A B : K → Finset (ZMod r)} (h : HasUniqueTaggedSums A B)
    (hAleave : unusedOrderedDifferences A = {1, -1})
    (hBleave : unusedOrderedDifferences B = {1, -1})
    (hAsidon : ∀ k, IsOrderedSidon (A k))
    (hBsidon : ∀ k, IsOrderedSidon (B k))
    (k : K) :
    (A k).card * ((A k).card - 1) +
      (B k).card * ((B k).card - 1) ≤ r - 3 := by
  rw [← card_orderedDifferenceSet_of_sidon (hAsidon k),
    ← card_orderedDifferenceSet_of_sidon (hBsidon k)]
  exact channel_difference_card_sum_le_sub_three
    hr3 h hAleave hBleave k

end

end Erdos85
