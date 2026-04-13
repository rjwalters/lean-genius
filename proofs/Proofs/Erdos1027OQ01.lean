/-!
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

## Key Sorries (3)

1. `card_subsets_containing`: bijection between `{A ⊆ B ⊆ X}` and `powerset(X \ A)`
   (via B ↦ X \ B or B ↦ B \ A; routine combinatorics)
2. `hbad_bound`: the union bound — bad subsets covered by ⋃_{A∈F} bad-due-to-A
   (needs: every non-good B witnesses some A ∈ F failing)
3. `hgood_bad`: `(goodSets F).card + badTotal.card = 2^|X|`
   (needs: goodSets F and bad subsets partition X.powerset)
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
    {A ⊆ B ⊆ X} to {Disjoint C A, C ⊆ X} (since A ⊆ B ↔ Disjoint (X \ B) A
    for B ⊆ X). -/
lemma card_subsets_containing (X A : Finset α) (hAX : A ⊆ X) :
    (X.powerset.filter (fun B => A ⊆ B)).card = 2 ^ (X.card - A.card) := by
  sorry  -- bijection via B ↦ X \ B; |(containing A)| = |(disjoint from A)| = 2^{|X|-|A|}

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
    -- Each non-good B is bad due to some A ∈ F. Union bound gives the result.
    sorry
  -- Step 2: goodSets + bad = 2^|X| (they partition X.powerset)
  have hgood_bad : (goodSets F).card + badTotal.card = 2 ^ X.card := by
    sorry
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
