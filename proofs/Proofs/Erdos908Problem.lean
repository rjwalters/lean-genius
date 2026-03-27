/-
Erdős Problem #908: Functions with Measurable Differences

Source: https://erdosproblems.com/908
Status: SOLVED (Laczkovich, 1980)

Statement:
Let f : ℝ → ℝ be such that f(x+h) - f(x) is measurable for every h > 0.
Is it true that f = g + h + r where:
- g is continuous
- h is additive (h(x+y) = h(x) + h(y))
- r(x+h) - r(x) = 0 for every h and almost all (depending on h) x

Answer: YES (Laczkovich, 1980)

Historical Context:
This was a conjecture of de Bruijn and Erdős concerning the structure of functions
whose differences are measurable. The conjecture asked whether such functions can
be decomposed into three canonical parts: a continuous function, an additive
function (which need not be continuous), and a "rigid" function that is almost
everywhere constant on every translate.

Key Insight:
The condition that f(x+h) - f(x) is measurable for all h is strictly weaker than
f itself being measurable. The decomposition theorem shows that the "non-measurable"
part of f must come from the additive component h.

References:
- [La80] Laczkovich, M., "Functions with measurable differences", Acta Math. Acad.
  Sci. Hungar. 35 (1980), 217-235.
- de Bruijn, N.G., "Functions whose differences belong to a given class",
  Nieuw Arch. Wisk. (1951).

Related: Erdős Problem #907 (on additive functions)

Tags: analysis, measure-theory, additive-functions, functional-equations
-/

import Mathlib.MeasureTheory.Function.AEMeasurableOrder
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Algebra.Group.Basic

open MeasureTheory Set

namespace Erdos908

/- ## Part I: Basic Definitions
-/

/-- A function f : ℝ → ℝ has measurable differences if for every h > 0,
    the difference function x ↦ f(x + h) - f(x) is Lebesgue measurable -/
def HasMeasurableDifferences (f : ℝ → ℝ) : Prop :=
  ∀ h : ℝ, h > 0 → Measurable (fun x => f (x + h) - f x)

/-- An additive function satisfies h(x + y) = h(x) + h(y) for all x, y -/
def IsAdditive (h : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, h (x + y) = h x + h y

/-- A function r is "rigid" if for every h, r(x+h) = r(x) for almost all x.
    The null set where this fails may depend on h. -/
def IsRigid (r : ℝ → ℝ) : Prop :=
  ∀ h : ℝ, ∀ᵐ x ∂volume, r (x + h) = r x

/- ## Part II: Properties of Additive Functions
-/

/-- Additive functions map 0 to 0 -/
theorem additive_zero (h : ℝ → ℝ) (hAdd : IsAdditive h) : h 0 = 0 := by
  have : h 0 = h (0 + 0) := by ring_nf
  rw [this, hAdd]
  ring

/-- Additive functions satisfy h(-x) = -h(x) -/
theorem additive_neg (h : ℝ → ℝ) (hAdd : IsAdditive h) (x : ℝ) : h (-x) = -h x := by
  have : h 0 = h (x + (-x)) := by ring_nf
  rw [hAdd] at this
  have h0 := additive_zero h hAdd
  linarith

/- ## Part III: Properties of Rigid Functions
-/

/- ## Part IV: The Decomposition Theorem
-/

/-- The main decomposition theorem (Laczkovich 1980).
    Any function with measurable differences decomposes as f = g + h + r
    where g is continuous, h is additive, and r is rigid.

    This was a conjecture of de Bruijn and Erdős.
    Laczkovich's proof uses deep measure-theoretic techniques. -/
axiom laczkovich_decomposition :
  ∀ (f : ℝ → ℝ), HasMeasurableDifferences f →
    ∃ (g h r : ℝ → ℝ),
      (Continuous g) ∧
      (IsAdditive h) ∧
      (IsRigid r) ∧
      (∀ x, f x = g x + h x + r x)

/- ## Part V: Special Cases
-/

/-- Continuous functions trivially have measurable differences -/
theorem continuous_has_measurable_differences (f : ℝ → ℝ) (hCont : Continuous f) :
    HasMeasurableDifferences f := by
  intro h _
  exact (hCont.sub hCont).measurable

/-- Additive functions have measurable differences (they're additive!) -/
theorem additive_has_measurable_differences (f : ℝ → ℝ) (hAdd : IsAdditive f) :
    HasMeasurableDifferences f := by
  intro h _
  -- f(x+h) - f(x) = f(x) + f(h) - f(x) = f(h), which is constant, hence measurable
  have : ∀ x, f (x + h) - f x = f h := fun x => by
    rw [hAdd]; ring
  simp_rw [this]
  exact measurable_const

/- ## Part VI: Connection to Related Problems
-/

/-- Erdős Problem #907: Related problem about additive functions.
    Asks about conditions ensuring additive functions are continuous. -/
def erdos_907_related : Prop :=
  -- If an additive function is bounded on any interval of positive length,
  -- then it is continuous
  ∀ (h : ℝ → ℝ), IsAdditive h →
    (∃ (a b : ℝ) (M : ℝ), a < b ∧ ∀ x ∈ Set.Ioo a b, |h x| ≤ M) →
    Continuous h

/- ## Part VII: The de Bruijn Perspective
-/

/-- de Bruijn's original formulation (1951): Which classes of functions
    are "difference closed" - if f(x+h) - f(x) ∈ C for all h, what can
    we say about f?

    For C = {measurable functions}, the answer is the decomposition theorem. -/
def DifferenceClosed (C : Set (ℝ → ℝ)) : Prop :=
  ∀ f : ℝ → ℝ, (∀ h : ℝ, h > 0 → (fun x => f (x + h) - f x) ∈ C) →
    ∃ (g h r : ℝ → ℝ), g ∈ C ∧ IsAdditive h ∧ IsRigid r ∧
      ∀ x, f x = g x + h x + r x

/- ## Part VIII: Summary
-/

/--
**Erdős Problem #908: SOLVED**

QUESTION: If f : ℝ → ℝ has measurable differences (f(x+h) - f(x) is measurable
for all h > 0), can f be decomposed as f = g + h + r where g is continuous,
h is additive, and r is rigid?

ANSWER: YES (Laczkovich, 1980)

KEY POINTS:
1. The decomposition exists and is essentially unique
2. The additive part h may be discontinuous (non-measurable)
3. The rigid part r satisfies r(x+h) = r(x) for a.e. x (depending on h)
4. This explains how non-measurability can arise from measurable differences

HISTORICAL SIGNIFICANCE:
- Resolved a conjecture of de Bruijn and Erdős
- Part of the theory of "difference equations" in analysis
- Connected to the study of additive (Hamel) functions
-/
theorem erdos_908_solved :
    ∀ (f : ℝ → ℝ), HasMeasurableDifferences f →
      ∃ (g h r : ℝ → ℝ),
        (Continuous g) ∧ (IsAdditive h) ∧ (IsRigid r) ∧
        (∀ x, f x = g x + h x + r x) := laczkovich_decomposition

/-- The de Bruijn-Erdős conjecture is true -/
theorem de_bruijn_erdos_conjecture :
    ∀ (f : ℝ → ℝ), HasMeasurableDifferences f →
      ∃ (g h r : ℝ → ℝ),
        (Continuous g) ∧ (IsAdditive h) ∧ (IsRigid r) ∧
        (∀ x, f x = g x + h x + r x) :=
  laczkovich_decomposition

/-- Summary of Erdős Problem #908 -/
theorem erdos_908_summary :
    -- The decomposition theorem holds
    (∀ f, HasMeasurableDifferences f →
      ∃ g h r, Continuous g ∧ IsAdditive h ∧ IsRigid r ∧ ∀ x, f x = g x + h x + r x) ∧
    -- Continuous functions satisfy the hypothesis trivially
    (∀ f, Continuous f → HasMeasurableDifferences f) ∧
    -- Additive functions satisfy the hypothesis
    (∀ f, IsAdditive f → HasMeasurableDifferences f) := by
  exact ⟨laczkovich_decomposition, continuous_has_measurable_differences,
         additive_has_measurable_differences⟩

end Erdos908
