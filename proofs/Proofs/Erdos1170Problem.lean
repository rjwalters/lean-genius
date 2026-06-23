/-
Erdős Problem #1170: Partition Properties of ω₂

Is it consistent that ω₂ → (α)²₂ for every α < ω₂?

That is, is it consistent with ZFC that for every ordinal α < ω₂ and every
2-coloring of pairs from ω₂, there exists a homogeneous subset of order type α?

Known Results:
- Laver (1982): Consistent that ω₂ → (ω₁² + 1, α)² for all α < ω₂
- Foreman and Hajnal (2003): Also proved consistency of ω₂ → (ω₁² + 1, α)²
  for all α < ω₂
- The full question (homogeneous for *both* colors, not just polarized) remains open

Context:
This is a problem in infinitary Ramsey theory / ordinal partition calculus.
The notation α → (β)ⁿ_k means: for every k-coloring of n-element subsets of α,
there exists a homogeneous set of order type β.
The question asks about the consistency (not provability) of this property,
meaning it involves forcing and independence results.

Formalization Notes:
- Partition relations are defined constructively using order-preserving embeddings
- Of the original 7 axioms, 6 have been eliminated (proved or replaced by defs)
- Only laver_consistency remains as axiom (deep forcing/independence result)

Reference: https://erdosproblems.com/1170
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Tactic

noncomputable section

open Cardinal Ordinal

namespace Erdos1170

-- ============================================================
-- PART 1: Ordinal Setup
-- ============================================================

/-- ω₁: the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1).ord

/-- ω₂: the second uncountable ordinal. -/
noncomputable def omega2 : Ordinal.{0} := (Cardinal.aleph 2).ord

/-- ω₁²: ordinal product ω₁ · ω₁. -/
noncomputable def omega1Sq : Ordinal.{0} := omega1 * omega1

-- ============================================================
-- PART 2: Partition Relation Definitions (Constructive)
-- ============================================================

/-- The balanced 2-color ordinal partition relation α → (β)²₂:
    for any 2-coloring of pairs from a well-ordered set of type α,
    there exists a β-length homogeneous chain (monochromatic in either color).

    Formally: there exists a strictly increasing function g from ordinals
    below β into ordinals below α such that all pairs receive the same color.
    The image of g is a homogeneous subset of order type β.

    This is stronger than the polarized relation α → (β, γ)² since
    we require the *same* order type β for both colors. -/
def ordinalPartitionBalanced (α β : Ordinal.{0}) : Prop :=
  ∀ f : Ordinal.{0} → Ordinal.{0} → Fin 2,
    ∃ (g : Ordinal.{0} → Ordinal.{0}) (c : Fin 2),
      (∀ i, i < β → g i < α) ∧
      (∀ i j, i < j → j < β → g i < g j) ∧
      (∀ i j, i < j → j < β → f (g i) (g j) = c)

/-- The polarized 2-color partition relation α → (β, γ)²:
    for any 2-coloring of pairs from α, there exists either a
    monochromatic-0 chain of length β or a monochromatic-1 chain of length γ.

    Formally: either there is a strictly increasing g from ordinals below β
    into ordinals below α with all pairs colored 0, or similarly for γ and color 1. -/
def ordinalPartitionPolarized (α β γ : Ordinal.{0}) : Prop :=
  ∀ f : Ordinal.{0} → Ordinal.{0} → Fin 2,
    (∃ g : Ordinal.{0} → Ordinal.{0},
      (∀ i, i < β → g i < α) ∧
      (∀ i j, i < j → j < β → g i < g j) ∧
      (∀ i j, i < j → j < β → f (g i) (g j) = 0)) ∨
    (∃ g : Ordinal.{0} → Ordinal.{0},
      (∀ i, i < γ → g i < α) ∧
      (∀ i j, i < j → j < γ → g i < g j) ∧
      (∀ i j, i < j → j < γ → f (g i) (g j) = 1))

-- ============================================================
-- PART 3: Basic Properties of Partition Relations (Proved)
-- ============================================================

/-- The balanced relation implies the polarized relation with equal targets. -/
theorem balanced_implies_polarized (α β : Ordinal.{0}) :
    ordinalPartitionBalanced α β → ordinalPartitionPolarized α β β := by
  intro h f
  obtain ⟨g, c, hbound, hmono, hcolor⟩ := h f
  fin_cases c
  · left; exact ⟨g, hbound, hmono, hcolor⟩
  · right; exact ⟨g, hbound, hmono, hcolor⟩

/-- Monotonicity: if α → (β)²₂ and β' ≤ β, then α → (β')²₂. -/
theorem balanced_mono_target (α β β' : Ordinal.{0}) :
    ordinalPartitionBalanced α β → β' ≤ β → ordinalPartitionBalanced α β' := by
  intro h hle f
  obtain ⟨g, c, hbound, hmono, hcolor⟩ := h f
  exact ⟨g, c,
    fun i hi => hbound i (lt_of_lt_of_le hi hle),
    fun i j hij hj => hmono i j hij (lt_of_lt_of_le hj hle),
    fun i j hij hj => hcolor i j hij (lt_of_lt_of_le hj hle)⟩

/-- Monotonicity in the source: if α → (β)²₂ and α ≤ α', then α' → (β)²₂. -/
theorem balanced_mono_source (α α' β : Ordinal.{0}) :
    ordinalPartitionBalanced α β → α ≤ α' → ordinalPartitionBalanced α' β := by
  intro h hle f
  obtain ⟨g, c, hbound, hmono, hcolor⟩ := h f
  exact ⟨g, c,
    fun i hi => lt_of_lt_of_le (hbound i hi) hle,
    hmono, hcolor⟩

-- ============================================================
-- PART 4: Main Problem Statement
-- ============================================================

/-- Erdős Problem #1170: The partition property of ω₂.
    The question asks whether it is *consistent* with ZFC that
    ω₂ → (α)²₂ for every α < ω₂.

    Note: This is a metamathematical question about consistency,
    not a question about provability in ZFC. We state the *property*
    here; the actual problem asks whether this property is consistent. -/
def erdos1170_property : Prop :=
    ∀ α : Ordinal.{0}, α < omega2 → ordinalPartitionBalanced omega2 α

-- ============================================================
-- PART 5: Known Results
-- ============================================================

/-- Laver's result (1982): It is consistent that the polarized
    relation ω₂ → (ω₁² + 1, α)² holds for all α < ω₂.
    This is weaker than the full balanced relation since it only
    guarantees order type ω₁² + 1 for the first color.

    This is a deep forcing/independence result that cannot be proved
    from ZFC alone — it requires large cardinal assumptions and
    iterated forcing constructions. -/
axiom laver_consistency :
    ∀ α : Ordinal.{0}, α < omega2 →
      ordinalPartitionPolarized omega2 (omega1Sq + 1) α

-- ============================================================
-- PART 6: Structural Observations (All Proved)
-- ============================================================

/-- ω₁ < ω₂: the first uncountable ordinal is less than the second. -/
theorem omega1_lt_omega2 : omega1 < omega2 := by
  unfold omega1 omega2
  exact Cardinal.ord_lt_ord.mpr (Cardinal.aleph_lt_aleph.mpr (by norm_num))

/-- ω₁² < ω₂: proved via cardinal arithmetic.
    card(ω₁²) = card(ω₁) · card(ω₁) = ℵ₁ · ℵ₁ = ℵ₁ < ℵ₂ = card(ω₂). -/
theorem omega1Sq_lt_omega2 : omega1Sq < omega2 := by
  unfold omega1Sq omega1 omega2
  rw [Cardinal.lt_ord, Ordinal.card_mul]
  simp only [Cardinal.card_ord]
  rw [Cardinal.mul_eq_self (le_of_lt (Cardinal.aleph0_lt_aleph 1))]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- Laver's result gives a polarized partition for ω₁² + 1 as first target. -/
theorem laver_gives_omega1Sq_partition :
    ordinalPartitionPolarized omega2 (omega1Sq + 1) omega1 := by
  exact laver_consistency omega1 omega1_lt_omega2

/-- If the full balanced property holds, Laver's polarized result follows
    as a special case (since balanced implies polarized). -/
theorem erdos1170_implies_laver_special :
    erdos1170_property →
    ∀ α : Ordinal.{0}, α < omega2 →
      ordinalPartitionPolarized omega2 α α := by
  intro h α hα
  exact balanced_implies_polarized omega2 α (h α hα)

end Erdos1170
