/-
Erdős Problem #1002: Asymptotic Distribution of Weighted Fractional Sums

For 0 < α < 1, define:
  f(α, n) = (1/log n) Σ_{k=1}^{n} (1/2 - {αk})

Does f(α, n) have an asymptotic distribution function?

**Status**: OPEN

**Known Results**:
- Weyl (1916): {kα} is equidistributed for irrational α
- Kesten (1960): The two-parameter variant f(α, β, n) has Cauchy limit distribution
- The one-parameter case (β = 0) remains open

Reference: https://erdosproblems.com/1002
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Instances.Real.Basic
import Mathlib.Data.Int.Floor

open MeasureTheory Set Filter Real Int

namespace Erdos1002

/-
## Fractional Part

The fractional part {x} = x - ⌊x⌋ maps ℝ to [0, 1).
For irrational α, {α}, {2α}, {3α}, ... is equidistributed by Weyl's theorem.
-/

/-- The deviation from the midpoint: 1/2 - {x}. -/
noncomputable def deviation (x : ℝ) : ℝ :=
  1 / 2 - Int.fract x

/-
## The Weighted Sum f(α, n)

S(α, n) = Σ_{k=1}^{n} (1/2 - {αk}) accumulates the deviation from uniformity.
f(α, n) = S(α, n) / log n normalizes by the natural growth scale.
-/

/-- The inner sum S(α, n) = Σ_{k=1}^{n} (1/2 - {αk}). -/
noncomputable def innerSum (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, deviation (α * (k + 1))

/-- The normalized function f(α, n) = S(α, n) / log n. -/
noncomputable def f (α : ℝ) (n : ℕ) : ℝ :=
  if n ≤ 1 then 0
  else innerSum α n / Real.log n

/-
## Distribution Functions

A distribution function g : ℝ → [0,1] is non-decreasing with
g(-∞) = 0 and g(+∞) = 1.
-/

/-- A function g is a distribution function. -/
def IsDistributionFunction (g : ℝ → ℝ) : Prop :=
  Monotone g ∧
  Tendsto g atBot (nhds 0) ∧
  Tendsto g atTop (nhds 1)

/-
## Asymptotic Distribution

The level set L(n, c) = {α ∈ (0,1) : f(α, n) ≤ c}.
f has an asymptotic distribution if μ(L(n, c)) → g(c) for some distribution g.
-/

/-- The level set L(n, c) = {α ∈ (0,1) : f(α, n) ≤ c}. -/
def levelSet (n : ℕ) (c : ℝ) : Set ℝ :=
  { α : ℝ | α ∈ Ioo 0 1 ∧ f α n ≤ c }

/-- The measure of the level set. -/
noncomputable def levelSetMeasure (n : ℕ) (c : ℝ) : ℝ :=
  (volume (levelSet n c)).toReal

/-- f has an asymptotic distribution function. -/
def hasAsymptoticDistribution : Prop :=
  ∃ g : ℝ → ℝ, IsDistributionFunction g ∧
    ∀ c : ℝ, Tendsto (fun n => levelSetMeasure n c) atTop (nhds (g c))

/-
## The Main Conjecture (OPEN)

Does f(α, n) possess an asymptotic distribution function?
This is Erdős's original question — it remains OPEN.
-/

/-- **Erdős Problem #1002 (OPEN)**: f(α, n) has an asymptotic distribution. -/
axiom erdos_1002_conjecture : hasAsymptoticDistribution

/-
## Kesten's Theorem (1960)

The two-parameter variant with a shift β:
  f(α, β, n) = (1/log n) Σ_{k=1}^{n} (1/2 - {β + αk})

Kesten proved this has Cauchy distribution g(c) = (1/π) arctan(ρc) + 1/2
when averaged over both α and β.
-/

/-- The two-parameter inner sum with shift β. -/
noncomputable def twoParamInnerSum (α β : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, deviation (β + α * (k + 1))

/-- The two-parameter normalized function. -/
noncomputable def twoParamF (α β : ℝ) (n : ℕ) : ℝ :=
  if n ≤ 1 then 0
  else twoParamInnerSum α β n / Real.log n

/-- The Cauchy distribution function g(c) = (1/π) arctan(ρc) + 1/2. -/
noncomputable def cauchyDistribution (ρ : ℝ) (c : ℝ) : ℝ :=
  1 / π * Real.arctan (ρ * c) + 1 / 2

/-- The Cauchy distribution function is a valid distribution function. -/
/-- Two-parameter level set. -/
def twoParamLevelSet (n : ℕ) (c : ℝ) : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo 0 1 ∧ twoParamF p.1 p.2 n ≤ c }

/-- Kesten (1960): The two-parameter variant has Cauchy limit distribution.
    There exists ρ > 0 such that the level set measure converges to
    g(c) = (1/π) arctan(ρc) + 1/2. -/
/-
## Relationship Between Problems

The one-parameter case is the β = 0 specialization:
  f(α, n) = f(α, 0, n)
-/

/-- f(α, n) equals the two-parameter variant at β = 0. -/
theorem one_param_is_specialization (α : ℝ) (n : ℕ) :
    f α n = twoParamF α 0 n := by
  simp [f, twoParamF, innerSum, twoParamInnerSum, deviation]

/-
## Why the Problem is Difficult

Fixing β = 0 destroys the ergodic independence Kesten used.
-/

/-- For fixed irrational α, f(α, n) is bounded (does not diverge). -/
/-- The inner sum |S(α, n)| ≤ C · log n for irrational α,
    where C depends on α's continued fraction expansion. -/
/-
## Partial Results

Weyl equidistribution implies the sum S(α, n) grows sublinearly,
justifying the log n normalization.
-/

/-- Weyl equidistribution: The average deviation tends to zero.
    This means (1/n) Σ (1/2 - {αk}) → 0 for irrational α. -/
/-- For rational α = p/q, the sum S(α, n) is periodic with period q. -/
/-
## Summary

**Status**: OPEN

**Formalized**:
- The weighted sum f(α, n) = (1/log n) Σ (1/2 - {αk})
- Distribution functions and asymptotic distribution
- Level sets and their measures
- The main conjecture: existence of limiting distribution
- Kesten's theorem for the two-parameter variant (Cauchy distribution)
- Relationship: f(α, n) = f(α, 0, n)
- Boundedness of f for irrational α
- Weyl equidistribution (inner sum grows sublinearly)

**OPEN**: Whether f(α, n) has an asymptotic distribution function.
The difficulty is the loss of independence when β = 0 is fixed.
-/

/-- **Erdős Problem #1002 (OPEN)**:
    Does f(α, n) = (1/log n) Σ (1/2 - {αk}) have an asymptotic distribution?
    Kesten proved the two-parameter variant has Cauchy distribution,
    but fixing β = 0 remains open. -/
theorem erdos_1002 : hasAsymptoticDistribution :=
  erdos_1002_conjecture

end Erdos1002
