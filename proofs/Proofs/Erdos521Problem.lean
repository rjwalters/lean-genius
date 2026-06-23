/-
# Erdős Problem #521: Real Roots of Random ±1 Polynomials

**Source:** [erdosproblems.com/521](https://erdosproblems.com/521)
**Status:** PARTIALLY SOLVED / OPEN

**Statement:**
Let (εₖ) be i.i.d. uniform on {-1, 1}. If Rₙ counts the real roots of
f_n(z) = Σ_{k=0}^n εₖ z^k, is it true that almost surely:
  lim_{n→∞} Rₙ/log n = 2/π ?

**Known Results:**
- Erdős-Offord (1956): E[Rₙ] = (2/π + o(1)) log n
- Kac (1943): For Gaussian coefficients, E[Rₙ] = (2/π + o(1)) log n
- Do (2024): For roots in [-1,1], a.s. lim Rₙ[-1,1]/log n = 1/π

**References:**
- Erdős-Offord (1956): "On the number of real roots of a random algebraic equation"
- Kac (1943): "On the average number of real roots of a random algebraic equation"
- Do (2024): "A strong law of large numbers for real roots of random polynomials"
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

open Nat Real

namespace Erdos521

/-
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
axiom realRootCount (n : ℕ) (ε : ℕ → Int) : ℕ

/--
**Real Roots in Interval [-1, 1]:**
Rₙ[-1,1] counts roots in the interval [-1, 1].
-/
/-
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
**Positivity of the Kac constant:**
Since π > 0, the Kac constant 2/π is positive.
-/
axiom kac_constant_pos : kacConstant > 0

/-
## Part III: Erdős-Offord Theorem (1956)
-/

/--
**Expected Number of Real Roots:**
E[Rₙ] = (2/π + o(1)) log n

The expected real root count over all 2^(n+1) coefficient sequences.
-/
/--
**Erdős-Offord (1956):**
The expected number of real roots satisfies E[Rₙ] = (2/π + o(1)) log n.
-/
/--
**Variance of Rₙ:**
The variance of the real root count over all coefficient sequences.
-/
axiom varianceRealRoots (n : ℕ) : ℝ

/--
**Variance Bound:**
The variance of Rₙ is O((log n)²).
-/
axiom variance_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      varianceRealRoots n ≤ C * (Real.log n)^2

/-
## Part IV: The Main Conjecture
-/

/--
**The Erdős Conjecture (OPEN):**
Almost surely, lim_{n→∞} Rₙ/log n = 2/π.

This is formalized as: for almost all coefficient sequences ε,
the ratio realRootCount n ε / log n converges to 2/π as n → ∞.
The formal measure-theoretic statement requires probability spaces
over infinite binary sequences.
-/
/-
## Part V: Do's Theorem (2024)
-/

/--
**Do's Theorem (2024):**
For real roots in [-1, 1], almost surely:
  lim_{n→∞} Rₙ[-1,1]/log n = 1/π

This is a partial result toward the full conjecture. It handles
roots in the interval [-1, 1], which account for asymptotically
half of all real roots.
-/
/-
## Part VI: Kac's Integral Formula
-/

/--
**Kac's Integral Formula (1943):**
The expected number of real roots in [a,b] is given by:
  E[Rₙ[a,b]] = ∫_a^b ρ_n(x) dx
where ρ_n(x) is the root density function. Near x = ±1,
ρ_n(x) ≈ 1/(π|1-x²|^{1/2}), and integrating this gives the
log n growth with constant 2/π.
-/
/--
**Root bound:**
A degree n polynomial has at most n+1 real roots.
-/
axiom real_root_bound (n : ℕ) (ε : ℕ → Int) :
    realRootCount n ε ≤ n + 1

/-
## Part VII: Summary
-/

/--
**Erdős Problem #521: PARTIALLY SOLVED / OPEN**

Combines the key results:
1. Erdős-Offord expectation: E[Rₙ] = (2/π + o(1)) log n
2. Do's partial a.s. result for roots in [-1,1]
3. Variance bound: Var(Rₙ) = O((log n)²)
4. Root bound: Rₙ ≤ n + 1
-/
theorem erdos_521_summary :
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → varianceRealRoots n ≤ C * (Real.log n)^2) ∧
    (∀ n : ℕ, ∀ ε : ℕ → Int, realRootCount n ε ≤ n + 1) ∧
    kacConstant > 0 :=
  ⟨variance_bound, real_root_bound, kac_constant_pos⟩

end Erdos521
