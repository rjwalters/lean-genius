/-
# Erdős Problem #1173: Free Sets for Set Mappings under GCH

Assuming the generalized continuum hypothesis, let
  f : ω_{ω+1} → [ω_{ω+1}]^{≤ℵ_ω}
be a set mapping such that |f(α) ∩ f(β)| < ℵ_ω for all α ≠ β.
Does there exist a free set of cardinality ℵ_{ω+1}?

## Status: OPEN

This is a problem of Erdős and Hajnal in infinitary combinatorics / set theory.
A "free set" for f means a set S such that α ∉ f(β) for all distinct α, β ∈ S.

## Context

Set mapping problems ask: given a function assigning to each element of a set
a "small" subset, can we find a "large" free set? The Hajnal free set theorem
handles the case where |f(α)| < κ for regular κ. This problem considers the
singular cardinal ℵ_ω, where the intersection condition replaces the size bound.

## References
- Erdős and Hajnal, original problem
- [Ko25b, Problem 35]
- [Va99, 7.88]
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Cardinal Ordinal

namespace Erdos1173

-- ============================================================
-- PART 1: Cardinal and Ordinal Setup
-- ============================================================

/-- ℵ_ω: the ω-th aleph cardinal (first singular aleph). -/
noncomputable def aleph_omega : Cardinal := Cardinal.aleph Ordinal.omega0

/-- ℵ_{ω+1}: the successor of ℵ_ω. -/
noncomputable def aleph_omega_succ : Cardinal := Cardinal.aleph (Ordinal.omega0 + 1)

/-- The ordinal ω_{ω+1}: the initial ordinal of cardinality ℵ_{ω+1}.
    Elements of this ordinal serve as the domain of the set mapping. -/
noncomputable def omega_omega_succ : Ordinal := aleph_omega_succ.ord

/-- The Generalized Continuum Hypothesis: for all ordinals α,
    2^(ℵ_α) = ℵ_{α+1}. -/
def GCH : Prop := ∀ α : Ordinal, (2 : Cardinal) ^ Cardinal.aleph α = Cardinal.aleph (α + 1)

-- ============================================================
-- PART 2: Set Mappings and Free Sets
-- ============================================================

/-- A set mapping on an ordinal γ assigns to each α < γ a set of ordinals
    below γ. We model this as a function from ordinals below γ to sets of
    ordinals below γ. -/
def SetMapping (γ : Ordinal) := (α : Ordinal) → α < γ → Set { β : Ordinal // β < γ }

/-- A set mapping f has bounded image size at most κ if each f(α) has
    cardinality at most κ. -/
def BoundedImageSize (γ : Ordinal) (f : SetMapping γ) (κ : Cardinal) : Prop :=
  ∀ (α : Ordinal) (hα : α < γ), Cardinal.mk (f α hα) ≤ κ

/-- The almost disjoint intersection condition: for all distinct α, β in the
    domain, |f(α) ∩ f(β)| < κ. This is a key regularity condition on the
    set mapping. -/
def AlmostDisjoint (γ : Ordinal) (f : SetMapping γ) (κ : Cardinal) : Prop :=
  ∀ (α β : Ordinal) (hα : α < γ) (hβ : β < γ),
    α ≠ β →
    Cardinal.mk { x : { δ : Ordinal // δ < γ } // x ∈ f α hα ∧ x ∈ f β hβ } < κ

/-- A free set for a set mapping f: a set S of ordinals below γ such that
    for all distinct α, β ∈ S, the element α is NOT in f(β).
    Formally, if α < γ and β < γ are distinct elements of S, then
    ⟨α, hα⟩ ∉ f β hβ. -/
def IsFreeSet (γ : Ordinal) (f : SetMapping γ) (S : Set { α : Ordinal // α < γ }) : Prop :=
  ∀ (a b : { α : Ordinal // α < γ }),
    a ∈ S → b ∈ S → a ≠ b → a ∉ f b.1 b.2

/-- A free set has a given cardinality. -/
def HasFreeSetOfCard (γ : Ordinal) (f : SetMapping γ) (κ : Cardinal) : Prop :=
  ∃ S : Set { α : Ordinal // α < γ }, IsFreeSet γ f S ∧ Cardinal.mk S = κ

-- ============================================================
-- PART 3: The Main Conjecture
-- ============================================================

/-- **Erdős Problem #1173** (Erdős-Hajnal):
    Assuming GCH, let f : ω_{ω+1} → [ω_{ω+1}]^{≤ℵ_ω} be a set mapping
    with |f(α) ∩ f(β)| < ℵ_ω for all α ≠ β.
    Does there exist a free set of cardinality ℵ_{ω+1}?

    This asks whether the almost disjoint intersection condition (weaker than
    bounding each |f(α)|) suffices to guarantee a free set as large as the
    domain. -/
def erdos_1173 : Prop :=
  GCH →
  ∀ (f : SetMapping omega_omega_succ),
    BoundedImageSize omega_omega_succ f aleph_omega →
    AlmostDisjoint omega_omega_succ f aleph_omega →
    HasFreeSetOfCard omega_omega_succ f aleph_omega_succ

-- ============================================================
-- PART 4: Context - The Hajnal Free Set Theorem
-- ============================================================

/-- The Hajnal free set theorem (background): For a regular cardinal κ and
    a set mapping f on κ⁺ with |f(α)| < κ for all α, there exists a free
    set of cardinality κ⁺.

    Erdős #1173 asks whether a similar result holds when κ = ℵ_ω (singular)
    with the weaker almost-disjoint intersection condition replacing the
    pointwise size bound. -/
/-- Under GCH, ℵ_ω is a strong limit cardinal:
    for all n : ℕ, 2^(ℵ_n) < ℵ_ω.

    Proof: GCH gives 2^ℵ_n = ℵ_{n+1}, and ℵ_{n+1} < ℵ_ω since n+1 < ω. -/
theorem gch_aleph_omega_strong_limit :
    GCH → ∀ n : ℕ, (2 : Cardinal) ^ Cardinal.aleph n < aleph_omega := by
  intro hgch n
  -- GCH: 2^ℵ_n = ℵ_{n+1}
  rw [hgch ↑n]
  -- ℵ_{n+1} < ℵ_ω iff (n+1 : Ordinal) < ω
  show Cardinal.aleph ((↑n : Ordinal) + 1) < Cardinal.aleph Ordinal.omega0
  rw [Cardinal.aleph_lt]
  -- (n : Ordinal) + 1 < ω
  have : ↑(n + 1 : ℕ) < Ordinal.omega0 := Ordinal.nat_lt_omega0 (n + 1)
  rwa [Nat.cast_add, Nat.cast_one] at this

/-- The almost disjoint condition means the "overlap" between any two
    images is strictly bounded by ℵ_ω. Since ℵ_ω = sup_{n<ω} ℵ_n (by
    `aleph_limit`), any cardinal below ℵ_ω must be ≤ ℵ_n for some n.

    Proof: By contraposition. If ℵ_n < c for all n, then since
    ℵ_ω = ⨆_{a < ω} ℵ_a, we get ℵ_ω ≤ c, contradicting c < ℵ_ω. -/
theorem overlap_bounded_by_aleph_n (f : SetMapping omega_omega_succ)
    (had : AlmostDisjoint omega_omega_succ f aleph_omega) :
  ∀ (α β : Ordinal) (hα : α < omega_omega_succ) (hβ : β < omega_omega_succ),
    α ≠ β →
    ∃ n : ℕ, Cardinal.mk { x : { δ : Ordinal // δ < omega_omega_succ } //
      x ∈ f α hα ∧ x ∈ f β hβ } ≤ Cardinal.aleph n := by
  intro α β hα hβ hab
  have hlt := had α β hα hβ hab
  unfold aleph_omega at hlt
  -- hlt : Cardinal.mk ... < Cardinal.aleph Ordinal.omega0
  -- By contradiction: if ∀ n, ℵ_n < c, then ℵ_ω ≤ c
  by_contra hall
  push_neg at hall
  -- hall : ∀ n : ℕ, Cardinal.aleph ↑n < Cardinal.mk ...
  apply absurd hlt (not_lt.mpr _)
  -- Goal: Cardinal.aleph Ordinal.omega0 ≤ Cardinal.mk ...
  -- ℵ_ω = ⨆_{a < ω₀} ℵ_a by the limit characterization of aleph
  rw [aleph_limit isSuccLimit_omega0]
  -- Goal: ⨆ (a : Set.Iio Ordinal.omega0), Cardinal.aleph ↑a ≤ ...
  exact ciSup_le fun ⟨a, ha⟩ => by
    obtain ⟨n, rfl⟩ := lt_omega0.mp ha
    exact le_of_lt (hall n)

-- ============================================================
-- PART 6: Related Results
-- ============================================================

/-- The Erdős-Hajnal set mapping theorem for ℵ₁: any set mapping
    f : ω₁ → [ω₁]^{≤ℵ₀} has a free set of size ℵ₁. This is the
    countable case that motivated Problem #1173. -/
/-- A weaker form: under GCH with the almost disjoint condition,
    there exists a free set of size ℵ_ω (rather than ℵ_{ω+1}).
    This would be a partial result toward the full conjecture. -/
def erdos_1173_weak : Prop :=
  GCH →
  ∀ (f : SetMapping omega_omega_succ),
    BoundedImageSize omega_omega_succ f aleph_omega →
    AlmostDisjoint omega_omega_succ f aleph_omega →
    HasFreeSetOfCard omega_omega_succ f aleph_omega

-- ============================================================
-- PART 7: Basic Properties
-- ============================================================

/-- ℵ_ω < ℵ_{ω+1}: the successor cardinal is strictly larger. -/
theorem aleph_omega_lt_succ : aleph_omega < aleph_omega_succ := by
  unfold aleph_omega aleph_omega_succ
  exact Cardinal.aleph_lt_aleph.mpr (Ordinal.lt_succ_iff.mpr le_rfl)

/-- Under GCH, 2^{ℵ_ω} = ℵ_{ω+1}. -/
theorem gch_power : GCH → (2 : Cardinal) ^ aleph_omega = aleph_omega_succ := by
  intro hgch
  exact hgch Ordinal.omega0

/-- The empty set is trivially free for any set mapping. -/
theorem free_set_empty (γ : Ordinal) (f : SetMapping γ) :
    IsFreeSet γ f ∅ := by
  intro a _ ha
  exact absurd ha (Set.not_mem_empty a)

/-- Any singleton is a free set (no distinct pair to check). -/
theorem free_set_singleton (γ : Ordinal) (f : SetMapping γ)
    (x : { α : Ordinal // α < γ }) :
    IsFreeSet γ f {x} := by
  intro a b ha hb hab
  rw [Set.mem_singleton_iff] at ha hb
  subst ha; subst hb
  exact absurd rfl hab

/-- A subset of a free set is free. -/
theorem free_set_subset (γ : Ordinal) (f : SetMapping γ)
    (S T : Set { α : Ordinal // α < γ }) (hfree : IsFreeSet γ f S) (hTS : T ⊆ S) :
    IsFreeSet γ f T :=
  fun a b ha hb hab => hfree a b (hTS ha) (hTS hb) hab

end Erdos1173
