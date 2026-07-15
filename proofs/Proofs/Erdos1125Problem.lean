/-
# Erdős Problem #1125: Kemperman's Inequality and Monotonicity

Source: https://erdosproblems.com/1125
Status: SOLVED (Laczkovich 1984)

Statement:
Let f : ℝ → ℝ be such that
  2f(x) ≤ f(x+h) + f(x+2h)
for every x ∈ ℝ and h > 0. Must f be monotonic?

Background:
- Kemperman (1969) posed this problem
- Kemperman proved YES if f is measurable
- Erdős wrote "if it were my problem I would offer $500 for it"
- Laczkovich (1984) proved YES unconditionally

Key Insight:
The inequality 2f(x) ≤ f(x+h) + f(x+2h) is a one-sided discrete convexity condition.
It says f cannot have a "local maximum" pattern at consecutive spacing h.
Laczkovich showed this forces global monotonicity even without measurability.

References:
- [Ke69] Kemperman, "On the regularity of generalized convex functions"
         Trans. Amer. Math. Soc. (1969), 69-93
- [La84] Laczkovich, "On Kemperman's inequality 2f(x) ≤ f(x+h) + f(x+2h)"
         Colloq. Math. (1984), 109-115
- [Er81b] Erdős, "My Scottish Book Problems", p. 31
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set MeasureTheory

namespace Erdos1125

/- ## Part I: The Kemperman Inequality

The condition 2f(x) ≤ f(x+h) + f(x+2h) for all x and h > 0.
-/

/-- **Kemperman Inequality:**
2f(x) ≤ f(x+h) + f(x+2h) for all x ∈ ℝ and h > 0. -/
def satisfiesKemperman (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2*h)

/-- **Alternative formulation:** f(x) - f(x+h) ≤ f(x+2h) - f(x).

    This is the correct rearrangement of 2f(x) ≤ f(x+h) + f(x+2h): moving one
    copy of f(x) to each side gives f(x) - f(x+h) ≤ f(x+2h) - f(x). (The earlier
    right-hand side f(x+h) - f(x+2h) was a sign typo — it is not equivalent to
    the Kemperman inequality.) -/
def satisfiesKempermanAlt (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ∀ h : ℝ, h > 0 → f x - f (x + h) ≤ f (x + 2*h) - f x

/-- The two formulations are equivalent. -/
theorem kemperman_equiv (f : ℝ → ℝ) :
    satisfiesKemperman f ↔ satisfiesKempermanAlt f := by
  constructor <;> intro hf x h hh <;> specialize hf x h hh <;> linarith

/- ## Part II: Monotonicity

A function is monotonic if it is either non-decreasing or non-increasing.
-/

/-- f is monotone non-decreasing on ℝ. -/
def isNonDecreasing (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ≤ y → f x ≤ f y

/-- f is monotone non-increasing on ℝ. -/
def isNonIncreasing (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ≤ y → f y ≤ f x

/-- f is monotonic (either non-decreasing or non-increasing). -/
def isMonotonic (f : ℝ → ℝ) : Prop :=
  isNonDecreasing f ∨ isNonIncreasing f

/- ## Part III: The Main Question -/

/-- **Kemperman's Question:**
Does satisfiesKemperman(f) imply isMonotonic(f)?

Kemperman proved YES when f is measurable.
The question for general f was the content of Erdős #1125. -/
def kemperman_question : Prop :=
  ∀ f : ℝ → ℝ, satisfiesKemperman f → isMonotonic f

/- ## Part IV: Kemperman's Partial Result (1969) -/

/-- **Kemperman's Theorem (1969):**
If f satisfies the Kemperman inequality AND is Lebesgue measurable,
then f is monotonic. -/
axiom kemperman_1969 (f : ℝ → ℝ) :
    satisfiesKemperman f → Measurable f → isMonotonic f

/- ## Part V: Laczkovich's Theorem (1984) -/

/-- **Laczkovich's Theorem (1984):**
If f : ℝ → ℝ satisfies 2f(x) ≤ f(x+h) + f(x+2h) for all x and h > 0,
then f is monotonic.

NO MEASURABILITY ASSUMPTION NEEDED.

This completely resolves Erdős Problem #1125. -/
axiom laczkovich_1984 :
    ∀ f : ℝ → ℝ, satisfiesKemperman f → isMonotonic f

/-- Laczkovich's theorem proves the Kemperman question is true. -/
theorem kemperman_question_resolved : kemperman_question :=
  laczkovich_1984

/- ## Part VI: Interpretation and Context -/

/-- The Kemperman inequality prevents certain "local maximum" patterns:
    the increment f(x+h) - f(x) is at least as large as the deficit f(x) - f(x+2h).
    Equivalently, f(x) - f(x+h) ≤ f(x+2h) - f(x). -/
theorem kemperman_interpretation (f : ℝ → ℝ) (hf : satisfiesKemperman f)
    (x h : ℝ) (hh : h > 0) :
    f x - f (x + h) ≤ f (x + 2*h) - f x := by
  have := hf x h hh
  linarith

/- ## Part VII: Examples -/

/-- Constant functions satisfy Kemperman. -/
theorem constant_satisfies (c : ℝ) : satisfiesKemperman (fun _ => c) := by
  intro x h _
  simp only
  linarith

/-- Non-decreasing linear functions f(x) = ax + b (with a ≥ 0) satisfy Kemperman.

    The `0 ≤ a` hypothesis is required: the Kemperman inequality
    2f(x) ≤ f(x+h) + f(x+2h) reduces here to 0 ≤ 3·a·h, which fails when a < 0.
    (This corrects an earlier version that dropped the sign hypothesis.) -/
theorem linear_satisfies (a b : ℝ) (ha : 0 ≤ a) :
    satisfiesKemperman (fun x => a * x + b) := by
  intro x h hh
  have : (0 : ℝ) ≤ 3 * a * h := by positivity
  simp only
  nlinarith [this]

/-- Any non-decreasing function satisfies Kemperman: if f x ≤ f (x+h) ≤ f (x+2h)
    then 2 f x ≤ f x + f (x+2h) ≤ f (x+h) + f (x+2h). This is the correct
    general source of examples (the Kemperman inequality is a one-sided condition
    that forbids local-maximum patterns, so monotone-up functions trivially
    satisfy it — whereas arbitrary convex functions such as x² do NOT). -/
theorem nonDecreasing_satisfies (f : ℝ → ℝ) (hf : isNonDecreasing f) :
    satisfiesKemperman f := by
  intro x h hh
  have h1 : f x ≤ f (x + h) := hf x (x + h) (by linarith)
  have h2 : f x ≤ f (x + 2 * h) := hf x (x + 2 * h) (by linarith)
  linarith

/-- The function f(x) = x² does **not** satisfy the Kemperman inequality:
    at x = -2h the second point pattern violates 2f(x) ≤ f(x+h) + f(x+2h).
    (Kemperman's 2f(x) ≤ f(x+h)+f(x+2h) is a one-sided condition, *not* midpoint
    convexity, so convex functions need not satisfy it.) -/
theorem square_not_satisfies : ¬ satisfiesKemperman (fun x => x ^ 2) := by
  intro h
  have := h (-2) 1 (by norm_num)
  norm_num at this

/- ## Part VIII: Summary

**Erdős Problem #1125 - SOLVED (Laczkovich 1984)**

**Problem (Kemperman):** If f : ℝ → ℝ satisfies 2f(x) ≤ f(x+h) + f(x+2h)
for all x and h > 0, must f be monotonic?

**Partial Result (Kemperman 1969):** Yes, if f is measurable.

**Full Resolution (Laczkovich 1984):** Yes, unconditionally.

**Key Insight:** The Kemperman inequality is a one-sided discrete convexity
condition that prevents "oscillating" behavior, forcing global monotonicity.

Erdős commented this would be worth $500 if it were his problem.
-/

/-- **Erdős Problem #1125: SOLVED**

Both Kemperman's partial result and Laczkovich's full resolution hold:
the Kemperman inequality forces monotonicity. -/
theorem erdos_1125 :
    (∀ f : ℝ → ℝ, satisfiesKemperman f → Measurable f → isMonotonic f) ∧
    (∀ f : ℝ → ℝ, satisfiesKemperman f → isMonotonic f) :=
  ⟨kemperman_1969, laczkovich_1984⟩

/-- Summary theorem: Kemperman's inequality implies monotonicity. -/
theorem erdos_1125_summary (f : ℝ → ℝ) :
    satisfiesKemperman f → isMonotonic f :=
  laczkovich_1984 f

end Erdos1125
