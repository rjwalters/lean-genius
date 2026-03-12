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
-- PART 2: Partition Relation Definitions
-- ============================================================

/-- The balanced 2-color ordinal partition relation α → (β)²₂:
    for any 2-coloring of pairs from α, there exists a homogeneous subset
    of order type β (monochromatic in either color).

    This is stronger than the polarized relation α → (β, γ)² since
    we require the *same* order type β for both colors. -/
axiom ordinalPartitionBalanced (α β : Ordinal.{0}) : Prop

/-- The polarized 2-color partition relation α → (β, γ)²:
    for any 2-coloring of pairs from α, there exists either a
    monochromatic-0 subset of order type β or a monochromatic-1
    subset of order type γ. -/
axiom ordinalPartitionPolarized (α β γ : Ordinal.{0}) : Prop

-- ============================================================
-- PART 3: Basic Properties of Partition Relations
-- ============================================================

/-- The balanced relation implies the polarized relation with equal targets. -/
axiom balanced_implies_polarized (α β : Ordinal.{0}) :
    ordinalPartitionBalanced α β → ordinalPartitionPolarized α β β

/-- Monotonicity: if α → (β)²₂ and β' ≤ β, then α → (β')²₂. -/
axiom balanced_mono_target (α β β' : Ordinal.{0}) :
    ordinalPartitionBalanced α β → β' ≤ β → ordinalPartitionBalanced α β'

/-- Monotonicity in the source: if α → (β)²₂ and α ≤ α', then α' → (β)²₂. -/
axiom balanced_mono_source (α α' β : Ordinal.{0}) :
    ordinalPartitionBalanced α β → α ≤ α' → ordinalPartitionBalanced α' β

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
    guarantees order type ω₁² + 1 for the first color. -/
axiom laver_consistency :
    ∀ α : Ordinal.{0}, α < omega2 →
      ordinalPartitionPolarized omega2 (omega1Sq + 1) α

-- ============================================================
-- PART 6: Structural Observations
-- ============================================================

/-- ω₁ < ω₂: the first uncountable ordinal is less than the second. -/
theorem omega1_lt_omega2 : omega1 < omega2 := by
  unfold omega1 omega2
  exact Cardinal.ord_lt_ord.mpr (Cardinal.aleph_lt_aleph.mpr (by norm_num))

/-- ω₁² < ω₂. -/
axiom omega1Sq_lt_omega2 : omega1Sq < omega2

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
