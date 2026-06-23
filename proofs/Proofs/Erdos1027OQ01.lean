/-
# Erdős Problem #1027 OQ-01: Quantitative Good-Set Lower Bound via Union Bound

## Open Question

Given that every n-uniform family F with |F| ≤ c · 2^n has Property B (Koishi Chan),
**OQ-01** asks for an explicit quantitative lower bound:

  `|goodSets F| ≥ 2^|X| - |F| · 2^{|X| - n + 1}`

where X = ∪F. This is the **union bound lower bound** on the number of good sets.

## Proof Strategy

For each A ∈ F (n-uniform), the "bad subsets due to A" satisfy:
  |{B ⊆ X : B ∩ A = ∅ ∨ A ⊆ B}| ≤ 2 · 2^{|X|-n}

because both `{B : Disjoint B A}` and `{B : A ⊆ B}` biject with `powerset(X \ A)`.

Union bound: total bad ≤ |F| · 2^{|X|-n+1}.
Conclusion: good ≥ 2^|X| - total bad ≥ 2^|X| - |F| · 2^{|X|-n+1}.

## Sorries Resolved

All 3 sorries proved:
1. `card_subsets_containing`: bijection via B ↦ X \ B involution
2. `hbad_bound`: union bound over bad-due-to-A sets
3. `hgood_bad`: goodSets and badTotal partition X.powerset
-/

import Mathlib
import Proofs.Erdos1027Problem

noncomputable section

namespace Erdos1027.UnionBound

open Finset Erdos1027

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================================
-- SECTION I: Counting Subsets Missing or Containing A
-- ============================================================

/-- Subsets of X disjoint from A biject with subsets of X \ A.
    Proof: B ⊆ X ∧ Disjoint B A ↔ B ⊆ X \ A (Finset.subset_sdiff). -/
lemma card_subsets_missing (X A : Finset α) (hAX : A ⊆ X) :
    (X.powerset.filter (fun B => Disjoint B A)).card = 2 ^ (X.card - A.card) := by
  have : X.powerset.filter (fun B => Disjoint B A) = (X \ A).powerset := by
    ext B; simp only [mem_filter, mem_powerset, subset_sdiff]
  rw [this, card_powerset, card_sdiff hAX]

/-- Subsets of X containing A biject with subsets of X \ A.
    Proof: the map B ↦ X \ B is an involution on X.powerset sending
    {A ⊆ B ⊆ X} bijectively to {C ⊆ X : Disjoint C A}. -/
lemma card_subsets_containing (X A : Finset α) (hAX : A ⊆ X) :
    (X.powerset.filter (fun B => A ⊆ B)).card = 2 ^ (X.card - A.card) := by
  rw [← card_subsets_missing X A hAX]
  -- The map B ↦ X \ B is an involution on X.powerset sending
  -- {A ⊆ B ⊆ X} bijectively to {C ⊆ X : Disjoint C A}
  apply Finset.card_bij (fun B _ => X \ B)
  · -- Well-definedness: A ⊆ B ⊆ X → X\B ⊆ X ∧ Disjoint (X\B) A
    intro B hB
    simp only [mem_filter, mem_powerset] at hB ⊢
    exact ⟨Finset.sdiff_subset, Finset.disjoint_left.mpr
      fun x hx hxA => (Finset.mem_sdiff.mp hx).2 (hB.2 hxA)⟩
  · -- Injectivity: X\B₁ = X\B₂ → B₁ = B₂ (via sdiff_sdiff_cancel_left)
    intro B₁ hB₁ B₂ hB₂ heq
    simp only [mem_filter, mem_powerset] at hB₁ hB₂
    rw [← sdiff_sdiff_cancel_left hB₁.1, heq, sdiff_sdiff_cancel_left hB₂.1]
  · -- Surjectivity: given C ⊆ X with Disjoint C A, take B = X\C
    intro C hC
    simp only [mem_filter, mem_powerset] at hC ⊢
    exact ⟨X \ C, ⟨Finset.sdiff_subset,
      fun x hxA => Finset.mem_sdiff.mpr ⟨hAX hxA, Finset.disjoint_left.mp hC.2 hxA⟩⟩,
      sdiff_sdiff_cancel_left hC.1⟩

/-- For A ⊆ X with A nonempty and |A| = n, bad-due-to-A has at most 2 · 2^{|X|-n} sets. -/
lemma card_bad_bound (X A : Finset α) (hAX : A ⊆ X) :
    (X.powerset.filter (fun B => Disjoint B A) ∪
     X.powerset.filter (fun B => A ⊆ B)).card ≤ 2 * 2 ^ (X.card - A.card) := by
  calc _ ≤ (X.powerset.filter (fun B => Disjoint B A)).card +
           (X.powerset.filter (fun B => A ⊆ B)).card := card_union_le _ _
    _ = 2 ^ (X.card - A.card) + 2 ^ (X.card - A.card) := by
        rw [card_subsets_missing X A hAX, card_subsets_containing X A hAX]
    _ = 2 * 2 ^ (X.card - A.card) := by ring

-- ============================================================
-- SECTION II: Main Theorem
-- ============================================================

/-- **Main Theorem (OQ-01)**: `2^|X| ≤ |goodSets F| + |F| · 2^{|X| - n + 1}`

    The classical Erdős-Hajnal Property B result follows as a corollary:
    if |F| · 2 < 2^n, then the RHS is < 2^|X|, so the LHS is ≥ 1. -/
theorem good_set_lower_bound (F : SetFamily α) (n : ℕ) (hn : 0 < n)
    (huniform : IsNUniform F n)
    (hsubset : ∀ A ∈ F, A ⊆ familyUnion F) :
    let X := familyUnion F
    2 ^ X.card ≤ (goodSets F).card + F.card * 2 ^ (X.card - n + 1) := by
  intro X
  set badTotal := X.powerset.filter (fun B => ¬IsGoodSet B F)
  -- Step 1: bad subsets covered by union of bad-due-to-A sets
  have hbad_bound : badTotal.card ≤ F.card * (2 * 2 ^ (X.card - n)) := by
    -- For each A ∈ F, define bad-due-to-A
    let badFor : Finset α → Finset (Finset α) := fun A =>
      X.powerset.filter (fun B => Disjoint B A ∨ A ⊆ B)
    -- Every non-good B is bad-due-to some A ∈ F
    have hcov : badTotal ⊆ F.biUnion badFor := by
      intro B hB
      rw [Finset.mem_biUnion]
      simp only [badTotal, mem_filter, mem_powerset] at hB
      obtain ⟨hBX, hBbad⟩ := hB
      -- Case split on whether B intersects all members of F
      by_cases hI : IntersectsAll B F
      · -- B intersects everything, so it must contain some A ∈ F
        have hnotC : ¬ContainsNone B F := fun h => hBbad ⟨hI, h⟩
        rw [ContainsNone] at hnotC; push_neg at hnotC
        obtain ⟨A, hAF, hA⟩ := hnotC
        exact ⟨A, hAF, mem_filter.mpr ⟨mem_powerset.mpr hBX, Or.inr hA⟩⟩
      · -- B misses some A ∈ F → Disjoint B A
        rw [IntersectsAll] at hI; push_neg at hI
        obtain ⟨A, hAF, hA⟩ := hI
        refine ⟨A, hAF, mem_filter.mpr ⟨mem_powerset.mpr hBX, Or.inl ?_⟩⟩
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact Finset.not_nonempty_iff_eq_empty.mp hA
    calc badTotal.card
        ≤ (F.biUnion badFor).card := Finset.card_le_card hcov
      _ ≤ F.sum (fun A => (badFor A).card) := Finset.card_biUnion_le
      _ ≤ F.sum (fun _ => 2 * 2 ^ (X.card - n)) := by
          apply Finset.sum_le_sum
          intro A hAF
          have hAX : A ⊆ X := hsubset A hAF
          have hAcard : A.card = n := huniform A hAF
          have hbadForEq : badFor A =
              X.powerset.filter (fun B => Disjoint B A) ∪
              X.powerset.filter (fun B => A ⊆ B) := by
            ext B; simp only [badFor, mem_filter, mem_union]; tauto
          rw [hbadForEq, ← hAcard]
          exact card_bad_bound X A hAX
      _ = F.card * (2 * 2 ^ (X.card - n)) := by
          simp [Finset.sum_const, mul_comm]
  -- Step 2: goodSets + bad = 2^|X| (they partition X.powerset)
  have hgood_bad : (goodSets F).card + badTotal.card = 2 ^ X.card := by
    have hgoodeq : goodSets F = X.powerset.filter (fun B => IsGoodSet B F) := by
      ext B; simp only [goodSets, mem_filter, mem_powerset, decide_eq_true_eq]
    have hbadeq : badTotal = X.powerset.filter (fun B => ¬IsGoodSet B F) := rfl
    rw [hgoodeq, hbadeq]
    have hdisj : Disjoint (X.powerset.filter (fun B => IsGoodSet B F))
                 (X.powerset.filter (fun B => ¬IsGoodSet B F)) := by
      rw [Finset.disjoint_left]
      intro B h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : X.powerset.filter (fun B => IsGoodSet B F) ∪
                 X.powerset.filter (fun B => ¬IsGoodSet B F) = X.powerset := by
      ext B; simp only [mem_union, mem_filter]; tauto
    rw [← Finset.card_union_of_disjoint hdisj, hunion, card_powerset]
  -- Step 3: conclude
  linarith [Nat.mul_le_mul_left F.card (show 2 * 2 ^ (X.card - n) ≤ 2 ^ (X.card - n + 1)
    from by rw [pow_succ]; ring_nf)]

/-- **Corollary**: If |F| · 2 < 2^n and F is n-uniform, then F has Property B.

    This recovers the classical Erdős-Hajnal bound as a corollary. -/
theorem property_b_from_union_bound (F : SetFamily α) (n : ℕ) (hn : 0 < n)
    (huniform : IsNUniform F n)
    (hsubset : ∀ A ∈ F, A ⊆ familyUnion F)
    (hFsmall : F.card * 2 < 2 ^ n)
    (hXbig : n ≤ (familyUnion F).card) :
    HasPropertyB F := by
  have hbound := good_set_lower_bound F n hn huniform hsubset
  -- Show |goodSets F| > 0
  have hpos : 0 < (goodSets F).card := by
    nlinarith [Nat.pos_pow_of_pos (n - 1) (by norm_num : 0 < 2),
              Nat.pos_pow_of_pos (familyUnion F).card (by norm_num : 0 < 2),
              Nat.sub_add_cancel hXbig,
              pow_add (2 : ℕ) ((familyUnion F).card - n) n]
  obtain ⟨B, hB⟩ := Finset.card_pos.mp hpos
  simp only [goodSets, mem_filter, mem_powerset, decide_eq_true_eq] at hB
  exact ⟨B, hB.1, hB.2.1, hB.2.2⟩

end Erdos1027.UnionBound
