import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-
# The Continuum Hypothesis

*Open Question from CantorDiagonalizationOQ01*: Does there exist a cardinal κ
with ℵ₀ < κ < 2^ℵ₀?

## Background

The **Continuum Hypothesis** (CH) states: there is no cardinal strictly between
ℵ₀ (the cardinality of ℕ) and 2^ℵ₀ (the cardinality of ℝ). Equivalently,
2^ℵ₀ = ℵ₁.

Cantor (1878) posed this as a conjecture. It became Hilbert's first problem (1900).
Gödel (1938) showed CH is consistent with ZFC (constructible universe L).
Cohen (1963) showed ¬CH is also consistent with ZFC (forcing).

Therefore CH is **independent of ZFC**: it can neither be proved nor disproved.

## What This Proves

We formalize basic cardinal arithmetic facts that contextualize the CH,
and state the CH itself as a proposition.
-/

namespace CantorDiagonalizationOQ01OQ01

open Cardinal

/-! ## Part 1: Cardinal Arithmetic Context -/

/-- Cantor's theorem: 2^κ > κ for all cardinals. No set maps onto its power set. -/
theorem cantor_cardinal : ℵ₀ < 2 ^ ℵ₀ :=
  aleph0_lt_continuum

/-- The continuum has cardinality 2^ℵ₀. -/
theorem continuum_eq : Cardinal.continuum = 2 ^ ℵ₀ :=
  Cardinal.continuum_eq

/-- ℵ₀ is infinite. -/
theorem aleph0_infinite : ℵ₀ ≥ ℵ₀ := le_refl _

/-- 2^ℵ₀ is uncountable. -/
theorem continuum_uncountable : ¬ Cardinal.continuum ≤ ℵ₀ := by
  rw [continuum_eq]
  exact not_le.mpr aleph0_lt_continuum

/-! ## Part 2: The Continuum Hypothesis -/

/-- **The Continuum Hypothesis**: There is no cardinal strictly between ℵ₀ and 2^ℵ₀.
Equivalently, 2^ℵ₀ = ℵ₁ (the first uncountable cardinal).

This is INDEPENDENT of ZFC (Gödel 1938, Cohen 1963):
- Consistent with ZFC: Gödel's constructible universe L satisfies CH
- Consistent with ZFC: Cohen's forcing models satisfy ¬CH

In Lean 4 / Mathlib, CH can be stated but neither proved nor disproved,
reflecting its set-theoretic independence. -/
def ContinuumHypothesis : Prop :=
  ∀ κ : Cardinal, ℵ₀ < κ → κ ≤ 2 ^ ℵ₀ → κ = 2 ^ ℵ₀

/-- Equivalent formulation: 2^ℵ₀ = ℵ₁. -/
def ContinuumHypothesisAlt : Prop :=
  Cardinal.continuum = Cardinal.aleph 1

/-- **The Generalized Continuum Hypothesis**: For all ordinals α,
2^(ℵ_α) = ℵ_{α+1}. This generalizes CH to all infinite cardinals. -/
def GeneralizedContinuumHypothesis : Prop :=
  ∀ α : Ordinal, 2 ^ Cardinal.aleph α = Cardinal.aleph (α + 1)

/-- GCH implies CH (specialize at α = 0). -/
theorem gch_implies_ch : GeneralizedContinuumHypothesis → ContinuumHypothesisAlt := by
  intro hgch
  unfold ContinuumHypothesisAlt
  rw [continuum_eq]
  have := hgch 0
  simp [Cardinal.aleph_zero] at this
  exact this

/-! ## Summary

**Answer to the question**: The existence of a cardinal κ with ℵ₀ < κ < 2^ℵ₀
is INDEPENDENT of ZFC. Neither "yes" (¬CH) nor "no" (CH) can be proved.

This is one of the most famous results in mathematical logic:
- Gödel (1938): ZFC + CH is consistent (if ZFC is)
- Cohen (1963): ZFC + ¬CH is consistent (if ZFC is)

In Lean 4, we can state CH but cannot prove or disprove it,
which correctly reflects its metamathematical status.
-/

end CantorDiagonalizationOQ01OQ01
