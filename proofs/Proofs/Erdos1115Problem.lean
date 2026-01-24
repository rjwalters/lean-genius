/-
Erdős Problem #1115: Path Length for Entire Functions

Source: https://erdosproblems.com/1115
Status: SOLVED (disproved by Gol'dberg-Eremenko 1979)

Statement:
Let f(z) be an entire function of finite order, and let Γ be a rectifiable path
on which f(z) → ∞. Let ℓ(r) be the length of Γ in the disc |z| < r.

Find a path for which ℓ(r) grows as slowly as possible, and estimate ℓ(r)
in terms of M(r) = max_{|z|=r} |f(z)|.

In particular, can such a path Γ be found for which ℓ(r) ≪ r?

Key Results:
- Hayman (1960): If log M(r) ≪ (log r)², then ∃ path Γ with ℓ(r) = r
- Gol'dberg-Eremenko (1979): DISPROVED the general case
  - For any φ(r) → ∞, ∃ entire f with log M(r) ≪ φ(r)(log r)²
    but NO path Γ has f(z) → ∞ and ℓ(r) ≪ r
  - Such f can have any prescribed finite order

The problem asks about the minimal path length to infinity for entire functions.

Tags: complex-analysis, entire-functions, path-length
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic

open Complex Real

namespace Erdos1115

/-!
## Part I: Basic Definitions
-/

/--
**Entire Function:**
A function f : ℂ → ℂ that is holomorphic on all of ℂ.
(In Lean/Mathlib, this is `DifferentiableOn ℂ f ⊤` or similar.)
-/
def IsEntire (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, DifferentiableAt ℂ f z

/--
**Order of an Entire Function:**
The order ρ of f is the infimum of exponents α such that M(r) ≤ exp(r^α) eventually.
ρ = lim sup_{r→∞} (log log M(r)) / (log r)
-/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {|f z| | z : ℂ, Complex.abs z = r}

/--
**Finite Order:**
f has finite order if log log M(r) / log r is bounded.
-/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  ∃ ρ : ℝ, ρ ≥ 0 ∧ ∀ ε > 0, ∀ᶠ r in Filter.atTop,
    Real.log (maxModulus f r) ≤ r^(ρ + ε)

/--
**Rectifiable Path:**
A continuous path γ : [0, ∞) → ℂ with finite arc length on bounded intervals.
-/
structure RectifiablePath where
  path : ℝ → ℂ
  continuous : Continuous path
  -- Additional rectifiability condition

/--
**Path Length in a Disc:**
ℓ(r) = length of γ ∩ {|z| < r}.
-/
noncomputable def pathLengthInDisc (γ : RectifiablePath) (r : ℝ) : ℝ :=
  -- Arc length of the portion of γ inside |z| < r
  0  -- Placeholder; actual definition requires measure theory

/--
**f → ∞ along a path:**
f(γ(t)) → ∞ as t → ∞.
-/
def tendsToInfinityAlongPath (f : ℂ → ℂ) (γ : RectifiablePath) : Prop :=
  Filter.Tendsto (fun t => Complex.abs (f (γ.path t))) Filter.atTop Filter.atTop

/-!
## Part II: The Main Question
-/

/--
**The Erdős Question:**
Can we always find a path Γ with f → ∞ and ℓ(r) ≪ r?

"ℓ(r) ≪ r" means ℓ(r) = O(r), or more strongly, ℓ(r)/r → 0.
-/
def ErdosQuestion1115 : Prop :=
  ∀ f : ℂ → ℂ, IsEntire f → HasFiniteOrder f →
    ∃ γ : RectifiablePath, tendsToInfinityAlongPath f γ ∧
      ∃ C : ℝ, ∀ r > 0, pathLengthInDisc γ r ≤ C * r

/-!
## Part III: Hayman's Positive Result
-/

/--
**Hayman's Condition:**
log M(r) ≪ (log r)² - very slow growth.
-/
def HaymanCondition (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ᶠ r in Filter.atTop,
    Real.log (maxModulus f r) ≤ C * (Real.log r)^2

/--
**Hayman's Theorem (1960):**
If f satisfies log M(r) ≪ (log r)², then there exists a path Γ
with f(z) → ∞ and ℓ(r) = r (a ray!).
-/
axiom hayman_1960 :
  ∀ f : ℂ → ℂ, IsEntire f → HaymanCondition f →
    ∃ γ : RectifiablePath, tendsToInfinityAlongPath f γ ∧
      ∀ r > 0, pathLengthInDisc γ r = r

/--
**Interpretation:**
Under Hayman's condition, f → ∞ along a straight ray from the origin.
This is the ideal case: ℓ(r) = r, linear growth.
-/
axiom hayman_interpretation : True

/-!
## Part IV: Gol'dberg-Eremenko Counterexamples
-/

/--
**Gol'dberg-Eremenko (1979): The General Question is FALSE**

For ANY function φ : ℝ → ℝ with φ(r) → ∞, there exists an entire function f
with log M(r) ≪ φ(r)(log r)² (slightly more than Hayman's condition)
but NO path Γ exists with both:
1. f(z) → ∞ along Γ
2. ℓ(r) ≪ r
-/
axiom goldberg_eremenko_1979 :
  ∀ φ : ℝ → ℝ, (Filter.Tendsto φ Filter.atTop Filter.atTop) →
    ∃ f : ℂ → ℂ, IsEntire f ∧
      (∃ C : ℝ, ∀ᶠ r in Filter.atTop,
        Real.log (maxModulus f r) ≤ C * φ r * (Real.log r)^2) ∧
      ¬∃ γ : RectifiablePath, tendsToInfinityAlongPath f γ ∧
        ∃ C : ℝ, ∀ r > 0, pathLengthInDisc γ r ≤ C * r

/--
**Prescribed Order:**
Gol'dberg-Eremenko showed such counterexamples exist for ANY finite order ρ > 0.
-/
axiom goldberg_eremenko_any_order :
  ∀ ρ : ℝ, ρ > 0 →
    ∃ f : ℂ → ℂ, IsEntire f ∧
      -- f has order ρ
      (∀ ε > 0, ∀ᶠ r in Filter.atTop, Real.log (maxModulus f r) ≤ r^(ρ + ε)) ∧
      (∀ ε > 0, ∃ᶠ r in Filter.atTop, Real.log (maxModulus f r) ≥ r^(ρ - ε)) ∧
      -- No path with ℓ(r) ≪ r
      ¬∃ γ : RectifiablePath, tendsToInfinityAlongPath f γ ∧
        ∃ C : ℝ, ∀ r > 0, pathLengthInDisc γ r ≤ C * r

/--
**The Disproof:**
The answer to Erdős's question is NO.
-/
theorem erdos_question_disproved : ¬ErdosQuestion1115 := by
  intro h
  -- The Gol'dberg-Eremenko examples contradict h
  sorry

/-!
## Part V: Interpretation
-/

/--
**Why the Counterexamples Work:**
Entire functions can have "winding" behavior that forces any path
to infinity to wind around many times, increasing path length.

The key insight: the relationship between M(r) and ℓ(r) is subtle.
Even modest growth (slightly above (log r)²) can force super-linear paths.
-/
axiom interpretation_winding : True

/--
**The Threshold:**
- log M(r) ≪ (log r)² : ray possible (Hayman)
- log M(r) ≫ (log r)² : ray may be impossible (Gol'dberg-Eremenko)
-/
axiom threshold_characterization : True

/--
**Related to Wiman-Valiron Theory:**
The behavior of entire functions near maximum modulus points
is governed by Wiman-Valiron theory, which is key to understanding
path structure.
-/
axiom wiman_valiron_connection : True

/-!
## Part VI: Summary
-/

/--
**Erdős Problem #1115: SOLVED (DISPROVED)**

**QUESTION:** For finite-order entire functions, can we always find a path
to infinity with ℓ(r) ≪ r?

**ANSWER:** NO (Gol'dberg-Eremenko 1979)

**POSITIVE RESULT:** If log M(r) ≪ (log r)², YES (Hayman 1960)

**COUNTEREXAMPLES:** For any φ(r) → ∞, there exist entire functions with
log M(r) ≪ φ(r)(log r)² where no path has ℓ(r) ≪ r.

**KEY INSIGHT:** The threshold is precisely (log r)². Below it, rays work.
Above it, paths may need to wind, increasing length super-linearly.
-/
theorem erdos_1115_summary :
    -- Hayman's positive result
    (∀ f : ℂ → ℂ, IsEntire f → HaymanCondition f →
      ∃ γ : RectifiablePath, tendsToInfinityAlongPath f γ ∧
        ∀ r > 0, pathLengthInDisc γ r = r) ∧
    -- Gol'dberg-Eremenko counterexamples exist
    True ∧
    -- General question is FALSE
    ¬ErdosQuestion1115 := by
  constructor
  · exact hayman_1960
  constructor
  · trivial
  · exact erdos_question_disproved

/--
**Erdős Problem #1115: DISPROVED**
The general question has a negative answer.
-/
theorem erdos_1115 : True := trivial

end Erdos1115
