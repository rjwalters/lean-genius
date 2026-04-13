/-
Erdős Problem #1169 — Open Question 4: Ordinal Partition Relation Properties

This file proves basic structural properties of ordinal partition relations
that were left as `def ..._prop : Prop` placeholders in Erdos1169Problem.lean.

## Theorems Proved

1. `omega1_uncountable`: ℵ₀ < ω₁.card (ω₁ is an uncountable ordinal)
2. `omega1_is_limit`: ω₁ is a limit ordinal (ord of infinite cardinal)
3. `omega_lt_omega1`: ω < ω₁ (all countable ordinals are below ω₁)
4. `omega1_regular`: ω₁ is a regular cardinal (cof(ω₁) = ℵ₁)
5. `omega1Sq_card`: ω₁² has cardinality ℵ₁ (infinite × infinite = infinite)
6. `partition_monotone_ordinal`: partition relation monotone in ordinal parameter
   (α → (β, k)² and γ ≤ β) → α → (γ, k)²

All proofs follow from Mathlib's cardinal arithmetic or directly from the
definition of `ordinalPartitionRel`.
-/

import Mathlib
import Proofs.Erdos1169Problem

namespace Erdos1169OQ04

open Cardinal Ordinal

-- ============================================================
-- PART 1: Basic Properties of ω₁
-- ============================================================

private lemma aleph0_lt_aleph1 : (ℵ₀ : Cardinal.{0}) < Cardinal.aleph 1 := by
  rw [show ℵ₀ = Cardinal.aleph 0 from Cardinal.aleph_zero.symm]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- ω₁ is an uncountable ordinal: ℵ₀ < ω₁.card. -/
theorem omega1_uncountable : Cardinal.aleph0 < omega1.card := by
  unfold omega1
  rw [Cardinal.card_ord]
  exact aleph0_lt_aleph1

/-- ω₁ is a limit ordinal. The ord of any infinite cardinal is limit. -/
theorem omega1_is_limit : Ordinal.IsLimit omega1 := by
  unfold omega1
  exact Cardinal.ord_isLimit (by
    rw [Cardinal.aleph_zero.symm]
    exact le_of_lt aleph0_lt_aleph1)

/-- ω < ω₁: every countable ordinal is strictly below ω₁. -/
theorem omega_lt_omega1 : Ordinal.omega < omega1 := by
  unfold omega1
  exact Cardinal.ord_lt_ord.mpr aleph0_lt_aleph1

/-- ω₁ is a regular cardinal: cof(ω₁.ord) = ω₁.card. -/
theorem omega1_regular : omega1.card.ord.cof = omega1.card := by
  unfold omega1
  rw [Cardinal.card_ord]
  exact Cardinal.isRegular_aleph_one.cof_eq

-- ============================================================
-- PART 2: Cardinality of ω₁²
-- ============================================================

/-- ω₁² = ω₁ · ω₁ has cardinality ℵ₁.
    Proof: card(ω₁ · ω₁) = card(ω₁) · card(ω₁) = ℵ₁ · ℵ₁ = ℵ₁. -/
theorem omega1Sq_card : omega1Sq.card = Cardinal.aleph 1 := by
  unfold omega1Sq omega1
  rw [Ordinal.card_mul, Cardinal.card_ord, Cardinal.card_ord]
  exact Cardinal.mul_eq_self aleph0_lt_aleph1.le

-- ============================================================
-- PART 3: Monotonicity of Partition Relations
-- ============================================================

/-- The partition relation α → (β, k)² is monotone decreasing in β:
    if α → (β, k)² and γ ≤ β, then α → (γ, k)².

    Proof: given a coloring c, apply the partition relation for β.
    If a red copy of type β exists (via f), restrict to the γ-prefix.
    If a blue k-clique exists, pass it through unchanged. -/
theorem partition_monotone_ordinal (α β γ : Ordinal) (k : ℕ)
    (hγβ : γ ≤ β) (h : ordinalPartitionRel α β k) :
    ordinalPartitionRel α γ k := by
  intro c
  rcases h c with ⟨f, hf_mono, hf_bound, hf_color⟩ | ⟨g, hg_mono, hg_bound, hg_color⟩
  · left
    exact ⟨f, hf_mono,
           fun i hi => hf_bound i (hi.trans_le hγβ),
           fun i j hij hjγ => hf_color i j hij (hjγ.trans_le hγβ)⟩
  · right; exact ⟨g, hg_mono, hg_bound, hg_color⟩

/-- Under CH, any β ≤ ω₁² satisfies β → (β, 3)²? No — but we can state
    the downward monotonicity corollary of Hajnal's theorem. -/
theorem hajnal_monotone_ordinal (h : CH) (γ : Ordinal) (hγ : γ ≤ omega1Sq) (k : ℕ) (hk : 2 ≤ k) :
    ordinalPartitionRel omega1Sq γ k :=
  partition_monotone_ordinal omega1Sq omega1Sq γ k hγ (hajnal_ch_implies_partition h k hk)

-- ============================================================
-- PART 4: Summary of Properties
-- ============================================================

/-- Confirmation that all placeholder propositions from Erdos1169Problem.lean hold. -/
theorem all_omega1_props :
    omega1_uncountable_prop ∧
    omega1Sq_card_prop ∧
    omega1_is_limit_prop ∧
    omega_lt_omega1_prop ∧
    omega1_regular_prop ∧
    partition_monotone_ordinal_prop := by
  refine ⟨omega1_uncountable, omega1Sq_card, omega1_is_limit, omega_lt_omega1,
          omega1_regular, ?_⟩
  intro α β γ k hγβ hαβ
  exact partition_monotone_ordinal α β γ k hγβ hαβ

end Erdos1169OQ04
