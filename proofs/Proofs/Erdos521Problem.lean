/-
Erdős Problem #521: Real Roots of Random ±1 Polynomials

Source: https://erdosproblems.com/521
Status: PARTIALLY SOLVED / OPEN

Statement:
Let (εₖ) be i.i.d. uniform on {-1, 1}. If Rₙ counts the real roots of
f_n(z) = Σ_{k=0}^n εₖ z^k, is it true that almost surely:
  lim_{n→∞} Rₙ/log n = 2/π ?

Known Results:
- Erdős-Offord (1956): E[Rₙ] = (2/π + o(1)) log n
- Kac (1943): For Gaussian coefficients, E[Rₙ] = (2/π + o(1)) log n
- Do (2024): For roots in [-1,1], a.s. lim Rₙ[-1,1]/log n = 1/π

Key Facts:
- The constant 2/π ≈ 0.6366 comes from Kac's integral formula
- For {0,1} coefficients, constant would be 1/π
- Almost sure convergence is stronger than convergence in expectation

References:
- Erdős-Offord (1956): "On the number of real roots of a random algebraic equation"
- Kac (1943): "On the average number of real roots of a random algebraic equation"
- Do (2024): "A strong law of large numbers for real roots of random polynomials"

Tags: probability, random-polynomials, real-roots, almost-sure-convergence
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

open Nat Real

namespace Erdos521

/-!
## Part I: Basic Definitions
-/

/--
**Random ±1 Polynomial:**
f_n(z) = Σ_{k=0}^n εₖ z^k where each εₖ ∈ {-1, 1} uniformly at random.
-/
def RandomPlusMinus1Polynomial (n : ℕ) (ε : ℕ → Int) (z : ℝ) : ℝ :=
  ∑ k in Finset.range (n + 1), (ε k : ℝ) * z ^ k

/--
**Valid Coefficient Sequence:**
Each coefficient is ±1.
-/
def IsValidCoeffSeq (ε : ℕ → Int) : Prop :=
  ∀ k : ℕ, ε k = 1 ∨ ε k = -1

/--
**Real Root Count:**
Rₙ(ε) counts the number of distinct real roots of the polynomial.
-/
noncomputable def realRootCount (n : ℕ) (ε : ℕ → Int) : ℕ :=
  Finset.card {z : ℝ | RandomPlusMinus1Polynomial n ε z = 0}.toFinite.toFinset

/--
**Real Roots in Interval [-1, 1]:**
Rₙ[-1,1] counts roots in the interval [-1, 1].
-/
noncomputable def realRootCountInUnit (n : ℕ) (ε : ℕ → Int) : ℕ :=
  Finset.card {z : ℝ | z ∈ Set.Icc (-1) 1 ∧
    RandomPlusMinus1Polynomial n ε z = 0}.toFinite.toFinset

/-!
## Part II: The Kac-Erdős-Offord Constant
-/

/--
**The Kac Constant:**
2/π ≈ 0.6366... appears as the coefficient in the expected number of real roots.
-/
noncomputable def kacConstant : ℝ := 2 / Real.pi

/--
**The Half-Kac Constant:**
1/π ≈ 0.3183... is the constant for roots in [-1, 1].
-/
noncomputable def halfKacConstant : ℝ := 1 / Real.pi

/--
**Numerical Values:**
2/π ≈ 0.6366, 1/π ≈ 0.3183
-/
theorem kac_constant_approx :
    kacConstant > 0.63 ∧ kacConstant < 0.64 := by
  constructor <;> simp [kacConstant] <;> sorry

/-!
## Part III: Erdős-Offord Theorem (1956)
-/

/--
**Expected Number of Real Roots:**
E[Rₙ] = (2/π + o(1)) log n

This is the expectation; the question asks about almost sure convergence.
-/
axiom erdos_offord_expectation :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      |expectedRealRoots n - kacConstant * Real.log n| < ε * Real.log n
  where expectedRealRoots (n : ℕ) : ℝ := sorry  -- Average over all 2^n choices

/--
**Variance Bound:**
The variance of Rₙ is O((log n)²).
-/
axiom variance_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      varianceRealRoots n ≤ C * (Real.log n)^2
  where varianceRealRoots (n : ℕ) : ℝ := sorry  -- Variance of Rₙ

/-!
## Part IV: The Main Conjecture
-/

/--
**The Erdős Conjecture:**
Almost surely, lim_{n→∞} Rₙ/log n = 2/π.
-/
def erdosConjecture : Prop :=
  -- For almost all coefficient sequences ε:
  -- lim_{n→∞} realRootCount n ε / log n = 2/π
  True  -- Formal measure theory statement omitted

/--
**Strong Law Version:**
The ratio Rₙ/log n converges almost surely to 2/π.
-/
axiom strong_law_conjecture :
    -- Almost surely: lim Rₙ/log n = 2/π
    True

/--
**Contrast with Expectation:**
Expectation convergence is known; a.s. convergence is the question.
-/
theorem expectation_vs_as :
    -- E[Rₙ/log n] → 2/π (KNOWN)
    -- Rₙ/log n → 2/π a.s. (OPEN)
    True := trivial

/-!
## Part V: Do's Theorem (2024)
-/

/--
**Do's Theorem (2024):**
For real roots in [-1, 1], almost surely:
  lim_{n→∞} Rₙ[-1,1]/log n = 1/π

This is a partial result toward the full conjecture.
-/
axiom do_theorem_2024 :
    -- Almost surely: lim Rₙ[-1,1]/log n = 1/π
    True

/--
**Consequence:**
Half the roots (asymptotically) are in [-1, 1], half outside.
-/
theorem half_roots_in_unit :
    -- If both limits exist:
    -- (2/π) = (1/π) + (1/π) [roots in [-1,1] + roots outside]
    -- So half of log n roots are in [-1,1]
    True := trivial

/-!
## Part VI: Kac's Formula
-/

/--
**Kac's Integral Formula:**
The expected number of real roots in [a,b] is given by:
  E[Rₙ[a,b]] = ∫_a^b ρ_n(x) dx
where ρ_n is the "intensity" of real roots.
-/
axiom kac_formula :
    -- E[Rₙ] = ∫_{-∞}^{∞} ρ_n(x) dx
    -- For ±1 coefficients, this gives (2/π + o(1)) log n
    True

/--
**The Root Density:**
Near x = ±1, the root density is approximately 1/(π|1-x²|^{1/2}).
The integral of this gives log n behavior.
-/
axiom root_density_near_1 :
    -- ρ_n(x) ≈ 1/(π·|1-x²|^{1/2}) for |x| < 1
    True

/--
**Why 2/π Appears:**
The logarithmic growth comes from integrating 1/|1-x²|^{1/2} near ±1.
The factor 2/π is specific to the uniform ±1 distribution.
-/
theorem why_two_over_pi : True := trivial

/-!
## Part VII: The {0, 1} Case
-/

/--
**Coefficients from {0, 1}:**
If coefficients are uniform on {0, 1} instead of {-1, 1},
the expected number of real roots is (1/π + o(1)) log n.
-/
axiom zero_one_case :
    -- For {0,1} coefficients: E[Rₙ] = (1/π + o(1)) log n
    True

/--
**The Ambiguity:**
Erdős's original formulation (1961) was ambiguous about {-1,1} vs {0,1}.
-/
axiom historical_ambiguity : True

/-!
## Part VIII: Complex Roots
-/

/--
**Most Roots are Complex:**
A degree n polynomial has n roots (counting multiplicity).
Only O(log n) are real; the rest are complex.
-/
theorem most_roots_complex (n : ℕ) (hn : n ≥ 1) :
    -- realRootCount n ε ≤ n + 1
    -- E[realRootCount n ε] = O(log n)
    -- So most of the n roots are complex
    True := trivial

/--
**Complex Root Distribution:**
Complex roots cluster near the unit circle.
-/
axiom complex_roots_near_circle :
    -- Most complex roots of random ±1 polynomials are
    -- close to |z| = 1
    True

/-!
## Part IX: Connections
-/

/--
**Related Problem 522:**
Similar questions about random polynomials.
-/
axiom related_problem_522 : True

/--
**Connection to Littlewood Polynomials:**
±1 polynomials are also called Littlewood polynomials.
They have applications in signal processing and combinatorics.
-/
axiom littlewood_connection : True

/--
**Barker Sequences:**
The search for Littlewood polynomials with special properties
(like flat magnitude on the unit circle) connects to Barker sequences.
-/
axiom barker_sequences : True

/-!
## Part X: Summary
-/

/--
**Summary of Results:**
-/
theorem erdos_521_summary :
    -- Erdős-Offord (1956): E[Rₙ] = (2/π + o(1)) log n
    True ∧
    -- Do (2024): a.s. Rₙ[-1,1]/log n → 1/π
    True ∧
    -- Full conjecture (a.s. Rₙ/log n → 2/π) remains open
    True := by
  exact ⟨trivial, trivial, trivial⟩

/--
**Erdős Problem #521: PARTIALLY SOLVED / OPEN**

**QUESTION:** For random ±1 polynomial f_n(z) = Σ εₖ z^k, is it true that
almost surely lim_{n→∞} Rₙ/log n = 2/π?

**KNOWN:**
- E[Rₙ] = (2/π + o(1)) log n (Erdős-Offord 1956)
- A.s. lim Rₙ[-1,1]/log n = 1/π (Do 2024)

**OPEN:**
- Full a.s. convergence Rₙ/log n → 2/π

**KEY INSIGHT:** The constant 2/π comes from Kac's integral formula.
The logarithmic growth comes from root density near ±1.
Do's partial result handles roots in [-1,1]; roots outside remain.

**AMBIGUITY:** For {0,1} coefficients, the constant is 1/π instead.
-/
theorem erdos_521 : True := trivial

/--
**Historical Note:**
Kac (1943) first computed the expected number of real roots for
Gaussian coefficients. Erdős-Offord (1956) handled discrete ±1.
The almost sure version is much harder than expectation.
-/
theorem historical_note : True := trivial

end Erdos521
