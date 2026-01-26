/-
Erdős Problem #120: The Similarity Problem

**Problem Statement (OPEN, $100 prize)**

Given an infinite set A ⊆ ℝ, must there exist a set E ⊆ ℝ of positive
Lebesgue measure that contains no similar copy of A?

A "similar copy" of A is any set aA + b = {a·x + b : x ∈ A} for a ≠ 0.

**Known Results:**
- Steinhaus (1920): FALSE for finite sets (every positive measure set
  contains a similar copy of any finite set)
- TRUE for unbounded A
- TRUE for A dense in some interval
- OPEN for bounded, nowhere-dense infinite sets (e.g., {1, 1/2, 1/4, ...})

**Status**: OPEN ($100 prize offered by Erdős)

Reference: https://erdosproblems.com/120

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set MeasureTheory Filter

namespace Erdos120

/-!
# Part 1: Similar Copies

A similar copy of A is the image of A under an affine map x ↦ a·x + b
with a ≠ 0. This preserves ratios between elements.
-/

/--
**Similar Copy of a Set**

Given A ⊆ ℝ and parameters a ≠ 0, b ∈ ℝ, the similar copy aA + b is
the set {a·x + b : x ∈ A}. This is a translated, scaled copy of A.
-/
def similarCopy (A : Set ℝ) (a b : ℝ) : Set ℝ :=
  (fun x => a * x + b) '' A

/--
**Contains a Similar Copy**

E contains a similar copy of A if there exist a ≠ 0 and b such that
aA + b ⊆ E. This is the inclusion of a full translated-scaled pattern.
-/
def containsSimilarCopy (E A : Set ℝ) : Prop :=
  ∃ a b : ℝ, a ≠ 0 ∧ similarCopy A a b ⊆ E

/--
**Avoids All Similar Copies**

E avoids all similar copies of A if no translate-scale of A fits inside E.
-/
def avoidsSimilarCopies (E A : Set ℝ) : Prop :=
  ¬ containsSimilarCopy E A

/-!
# Part 2: Universal Similarity Sets

A set A is "universal" if every positive-measure set must contain a
similar copy of A. Finite sets are universal (Steinhaus).
-/

/--
**Universal Similarity Set**

A is universal if every measurable set E with μ(E) > 0 contains
a similar copy of A.
-/
def universalSimilaritySet (A : Set ℝ) : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → volume E > 0 →
    containsSimilarCopy E A

/--
**Avoidable Set**

A is avoidable if there exists a measurable set E with μ(E) > 0
containing no similar copy of A.
-/
def avoidable (A : Set ℝ) : Prop :=
  ∃ E : Set ℝ, MeasurableSet E ∧ volume E > 0 ∧
    avoidsSimilarCopies E A

/-!
# Part 3: Steinhaus Theorem (Finite Sets are Universal)

The classical Steinhaus theorem (1920) implies that finite sets
are universal similarity sets.
-/

/--
**Steinhaus (1920): Finite Sets are Universal**

If A is a finite nonempty subset of ℝ, then every set E with
positive Lebesgue measure contains a similar copy of A.

The proof uses the Steinhaus theorem: if μ(E) > 0, then E - E
contains an interval around 0. For a finite set, this provides
enough room to embed any pattern.
-/
axiom steinhaus_finite (A : Set ℝ) (hA : A.Finite) (hne : A.Nonempty) :
    universalSimilaritySet A

/-!
# Part 4: Known Avoidable Cases

Two classes of infinite sets are known to be avoidable.
-/

/--
**Unbounded Sets are Avoidable**

If A is unbounded, then A is avoidable. A positive-measure set
E can be constructed (e.g., within a bounded interval) that
cannot contain similar copies with arbitrarily large elements.
-/
axiom unbounded_avoidable (A : Set ℝ) (hA : ¬ Bornology.IsBounded A) :
    avoidable A

/--
**Sets Dense in an Interval are Avoidable**

If A is dense in some open interval (a,b), then A is avoidable.
The density forces similar copies to "fill up" intervals, which
can be avoided by careful measure-theoretic constructions.
-/
axiom dense_in_interval_avoidable (A : Set ℝ)
    (hDense : ∃ a b : ℝ, a < b ∧ Dense ((A ∩ Set.Ioo a b) : Set ℝ)) :
    avoidable A

/-!
# Part 5: The Erdős Conjecture

The central open problem: every infinite set is avoidable.
-/

/--
**Erdős Problem #120 (OPEN, $100)**

Every infinite set A ⊆ ℝ is avoidable.

Equivalently: for every infinite A, there exists a measurable set
E with positive Lebesgue measure containing no similar copy of A.

This is equivalent to saying: no infinite set is a universal
similarity set.
-/
def erdos_120_conjecture : Prop :=
  ∀ A : Set ℝ, A.Infinite → avoidable A

/--
**Negation: There exists a universal infinite set**

The negation would mean some infinite set appears as a similar
copy inside every positive-measure set.
-/
def erdos_120_negation : Prop :=
  ∃ A : Set ℝ, A.Infinite ∧ universalSimilaritySet A

/-!
# Part 6: The Geometric Sequence Case

The key test case: A = {1, 1/2, 1/4, ...} = {(1/2)^n : n ∈ ℕ}.
-/

/--
**Geometric Sequence {(1/2)^n : n ∈ ℕ}**

This is the set {1, 1/2, 1/4, 1/8, ...}. It is bounded,
converges to 0, and has specific ratio structure (each element
is half the previous one).
-/
def geometricSeq : Set ℝ := {x | ∃ n : ℕ, x = (1/2 : ℝ)^n}

/-- The geometric sequence is infinite. -/
axiom geometricSeq_infinite : geometricSeq.Infinite

/-- The geometric sequence is bounded. -/
axiom geometricSeq_bounded : Bornology.IsBounded geometricSeq

/--
**The Geometric Sequence Case (OPEN)**

Is the geometric sequence {(1/2)^n : n ∈ ℕ} avoidable?

This is Problem 94 on Ben Green's open problems list. If resolved,
it would be a major breakthrough toward the full conjecture.
-/
def erdos_120_geometric : Prop := avoidable geometricSeq

/-!
# Part 7: Ratio Invariance

Similar copies preserve ratios between elements, which constrains
where copies can appear inside a set E.
-/

/--
**Ratio Preservation**

For a similar copy aA + b, the ratio (aᵢ - aⱼ)/(aₖ - aₗ) is
preserved for all elements aᵢ, aⱼ, aₖ, aₗ ∈ A.

This means: if x₁ = a·a₁ + b and x₂ = a·a₂ + b, then
x₁ - x₂ = a(a₁ - a₂), so ratios of differences are invariant.
-/
theorem ratio_preserved (A : Set ℝ) (a b : ℝ) (ha : a ≠ 0)
    (a₁ a₂ a₃ a₄ : ℝ) (h₁ : a₁ ∈ A) (h₂ : a₂ ∈ A)
    (h₃ : a₃ ∈ A) (h₄ : a₄ ∈ A) (h₃₄ : a₃ ≠ a₄) :
    (a * a₁ + b - (a * a₂ + b)) / (a * a₃ + b - (a * a₄ + b)) =
    (a₁ - a₂) / (a₃ - a₄) := by
  ring_nf
  rw [mul_div_mul_left _ _ ha]

/-!
# Part 8: Measure-Theoretic Tools

Key tools from measure theory that relate to this problem.
-/

/--
**Steinhaus Difference Theorem**

If E has positive Lebesgue measure, then E - E = {x - y : x, y ∈ E}
contains an open interval around 0.

This is the classical result underlying the universality of finite sets.
-/
axiom steinhaus_difference (E : Set ℝ) (hE : MeasurableSet E)
    (hpos : volume E > 0) :
    ∃ δ > 0, Set.Ioo (-δ) δ ⊆ {z | ∃ x y, x ∈ E ∧ y ∈ E ∧ z = x - y}

/--
**Lebesgue Density Theorem**

For a measurable set E, almost every point of E is a point of
density 1. This constrains the local structure of positive-measure sets.
-/
axiom lebesgue_density (E : Set ℝ) (hE : MeasurableSet E) (hpos : volume E > 0) :
    ∃ x ∈ E, ∀ ε > 0,
    volume (E ∩ Set.Ioo (x - ε) (x + ε)) / volume (Set.Ioo (x - ε) (x + ε)) > 1/2

/-!
# Part 9: Connections and Related Problems
-/

/--
**Relationship Between Universal and Avoidable**

A is universal iff A is not avoidable.
These are complementary properties.
-/
theorem universal_iff_not_avoidable (A : Set ℝ) :
    universalSimilaritySet A ↔ ¬ avoidable A := by
  constructor
  · intro hUniv ⟨E, hMeas, hPos, hAvoid⟩
    exact hAvoid (hUniv E hMeas hPos)
  · intro hNotAvoid
    by_contra hNotUniv
    push_neg at hNotUniv
    obtain ⟨E, hMeas, hPos, hNot⟩ := hNotUniv
    exact hNotAvoid ⟨E, hMeas, hPos, hNot⟩

/--
**The Conjecture Equivalently**

erdos_120_conjecture ↔ no infinite set is universal.
-/
theorem conjecture_equiv :
    erdos_120_conjecture ↔ ∀ A : Set ℝ, A.Infinite → ¬ universalSimilaritySet A := by
  unfold erdos_120_conjecture
  constructor
  · intro h A hInf hUniv
    have := h A hInf
    rw [universal_iff_not_avoidable] at hUniv
    exact hUniv this
  · intro h A hInf
    rw [← not_not (avoidable A)]
    rw [← universal_iff_not_avoidable]
    exact fun hUniv => h A hInf hUniv

/-!
# Part 10: Summary
-/

/-- The problem is OPEN with a $100 prize. -/
def erdos_120_status : String := "OPEN ($100 prize)"

/-- The known landscape: finite = universal, unbounded/dense = avoidable. -/
theorem erdos_120_known_results :
    -- Finite nonempty sets are universal
    (∀ A : Set ℝ, A.Finite → A.Nonempty → universalSimilaritySet A) ∧
    -- Unbounded sets are avoidable
    (∀ A : Set ℝ, ¬ Bornology.IsBounded A → avoidable A) := by
  exact ⟨steinhaus_finite, unbounded_avoidable⟩

/-!
# Summary

**Problem:** For every infinite A ⊆ ℝ, does there exist E with μ(E) > 0
containing no similar copy aA + b (a ≠ 0)?

**Status:** OPEN ($100 prize)

**Known:**
- Finite sets: UNIVERSAL (Steinhaus 1920)
- Unbounded sets: AVOIDABLE
- Sets dense in intervals: AVOIDABLE
- Geometric sequence {1, 1/2, 1/4, ...}: OPEN (Green's Problem 94)

**Tools:** Steinhaus difference theorem, Lebesgue density theorem,
ratio invariance of similar copies

**Source:** Erdős, referenced in Svetic (2000), Jung-Lai-Mooroogen (2024)
-/

end Erdos120
