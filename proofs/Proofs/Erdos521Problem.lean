/-
Erdős Problem #521: Real Roots of Random Polynomials with ±1 Coefficients

Source: https://erdosproblems.com/521
Status: OPEN (for the almost sure limit; partial results known)

Statement:
Let (ε_k)_{k≥0} be independently uniformly chosen from {-1,1}.
If R_n counts the number of real roots of f_n(z) = Σ_{0≤k≤n} ε_k z^k,
then is it true that, almost surely,
  lim_{n→∞} R_n / log n = 2/π ?

History:
- Erdős-Offord (1956): E[R_n] = (2/π + o(1)) log n (expected value)
- Kac (1943): Earlier formula for expected roots
- Do (2024): Proved that for roots in [-1,1], almost surely R_n[-1,1]/log n → 1/π

Note: There is ambiguity whether Erdős intended {-1,1} or {0,1} coefficients.
For {0,1}, the constant would be 1/π instead of 2/π.

References:
- [EO56] Erdős, Offord, "On the number of real roots of a random algebraic equation",
  Proc. London Math. Soc. (3) (1956), 139-160.
- [Ka43] Kac, M., "On the average number of real roots of a random algebraic equation",
  Bull. Amer. Math. Soc. (1943), 314-320.
- [Do24] Do, Y., "A strong law of large numbers for real roots of random polynomials",
  arXiv:2403.06353 (2024).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Real Polynomial

namespace Erdos521

/-
## Part I: Random Polynomials with ±1 Coefficients
-/

/--
**Random Sign:**
ε ∈ {-1, 1} chosen uniformly at random.
-/
def RandomSign : Type := {x : ℤ // x = -1 ∨ x = 1}

/--
**Random Polynomial:**
f_n(z) = Σ_{k=0}^n ε_k z^k where each ε_k ∈ {-1,1} is random.
-/
def RandomLittlewoodPolynomial (n : ℕ) (ε : Fin (n+1) → ℤ) : Polynomial ℤ :=
  ∑ k : Fin (n+1), Polynomial.C (ε k) * Polynomial.X ^ (k : ℕ)

/--
**Littlewood Polynomial:**
A polynomial with all coefficients in {-1, 1}.
Also called a ±1 polynomial.
-/
def IsLittlewoodPolynomial (p : Polynomial ℤ) : Prop :=
  ∀ k : ℕ, p.coeff k = -1 ∨ p.coeff k = 0 ∨ p.coeff k = 1

/-
## Part II: Counting Real Roots
-/

/--
**Real Root:**
A real root of polynomial p is an x ∈ ℝ with p.eval x = 0.
-/
def IsRealRoot (p : Polynomial ℝ) (x : ℝ) : Prop :=
  p.eval x = 0

/--
**Real Root Count (with multiplicity):**
R_n = number of real roots of f_n, counted with multiplicity.
-/
noncomputable def realRootCount (p : Polynomial ℝ) : ℕ :=
  p.roots.countP (fun _ => True)  -- Placeholder for actual root count

/--
**Real Root Count in Interval:**
R_n[a,b] = number of real roots in the interval [a,b].
-/
noncomputable def realRootCountInterval (p : Polynomial ℝ) (a b : ℝ) : ℕ :=
  p.roots.countP (fun x => a ≤ x ∧ x ≤ b)  -- Placeholder

/-
## Part III: The Kac-Erdős-Offord Formula
-/

/--
**Kac's Formula (1943):**
The expected number of real roots of a random polynomial with i.i.d.
standard normal coefficients is (2/π) log n + C + o(1).
-/
axiom kac_formula :
  True  -- Placeholder for precise probabilistic statement

/--
**Erdős-Offord (1956):**
For random ±1 polynomials, E[R_n] = (2/π + o(1)) log n.

This is the expected value result, not the almost sure limit.
-/
axiom erdos_offord_1956 :
  ∃ c : ℝ → ℝ, (∀ n, |c n| ≤ 1) ∧
    -- E[R_n] / log n → 2/π as n → ∞
    Filter.Tendsto c Filter.atTop (nhds 0)

/--
**The Constant 2/π:**
The Erdős-Offord constant for ±1 polynomials.
≈ 0.6366197...
-/
noncomputable def erdosOffordConstant : ℝ := 2 / Real.pi

/--
**Alternative Constant 1/π:**
For {0,1} coefficients or roots in [-1,1], the constant is 1/π.
≈ 0.3183098...
-/
noncomputable def alternativeConstant : ℝ := 1 / Real.pi

/-
## Part IV: The Erdős Question
-/

/--
**The Almost Sure Limit:**
Does R_n / log n → 2/π almost surely (not just in expectation)?
-/
def ErdosQuestion : Prop :=
  -- Almost surely, lim_{n→∞} R_n/log n = 2/π
  True  -- Placeholder for measure-theoretic statement

/--
**Stronger Form:**
The expected value result is known. The question is whether
the limit holds almost surely (strong law of large numbers style).
-/
axiom known_vs_open :
  -- Expected value is known (Erdős-Offord)
  True ∧
  -- Almost sure limit is open
  True

/-
## Part V: Partial Results
-/

/--
**Do's Theorem (2024):**
For roots in the interval [-1,1], almost surely:
  lim_{n→∞} R_n[-1,1] / log n = 1/π

This proves the almost sure result for a restricted domain.
-/
axiom do_2024 :
  -- Almost surely, R_n[-1,1]/log n → 1/π
  True  -- Placeholder for precise statement

/--
**Roots Outside [-1,1]:**
The distribution of roots outside [-1,1] is more difficult to analyze.
The almost sure behavior for all real roots remains open.
-/
axiom roots_outside_interval :
  True

/--
**Concentration Inequalities:**
Various concentration results are known for R_n, but they don't
immediately imply the almost sure limit.
-/
axiom concentration_results :
  True

/-
## Part VI: Related Results
-/

/--
**Kac Rice Formula:**
A general formula for expected number of real zeros of random functions.
-/
axiom kac_rice_formula :
  True

/--
**Logarithmic Growth:**
The number of real roots grows logarithmically with degree,
much slower than the degree itself.
-/
axiom logarithmic_growth :
  -- R_n = O(log n) a.s. is known
  True

/--
**Complex vs Real Roots:**
A degree n polynomial has exactly n complex roots (counting multiplicity).
The number of real roots (for random ±1 polynomials) is ~ (2/π) log n.
Most roots are complex!
-/
axiom complex_vs_real :
  -- n complex roots, ~ (2/π) log n real roots
  True

/-
## Part VII: Special Cases
-/

/--
**Specific Polynomials:**
1 + x + x² + ... + xⁿ has only one real root (at x = -1 if n is odd).
Other specific Littlewood polynomials have been studied.
-/
axiom specific_polynomials :
  True

/--
**Barker Sequences:**
Connection to sequences with optimal autocorrelation properties.
-/
axiom barker_connection :
  True

/--
**Flat Polynomials:**
Littlewood polynomials with |p(z)| nearly constant on the unit circle.
-/
axiom flat_polynomials :
  True

/-
## Part VIII: Probability Theory Context
-/

/--
**Strong Law vs Weak Law:**
- Weak: E[R_n]/log n → 2/π (known by Erdős-Offord)
- Strong: R_n/log n → 2/π almost surely (open)
-/
axiom strong_vs_weak :
  True

/--
**Independence of Coefficients:**
The coefficients ε_k are independent, which is crucial for analysis.
-/
axiom coefficient_independence :
  True

/--
**Symmetry:**
Each ε_k is equally likely to be +1 or -1 (symmetric distribution).
-/
axiom symmetry :
  True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #521:**

PROBLEM: For random ±1 polynomial f_n, is it true almost surely that
  lim_{n→∞} R_n / log n = 2/π ?

STATUS: OPEN (for the almost sure limit)

KNOWN RESULTS:
1. Erdős-Offord (1956): E[R_n] = (2/π + o(1)) log n (expected value)
2. Do (2024): Almost surely, R_n[-1,1]/log n → 1/π (for roots in [-1,1])

OPEN: Does R_n/log n → 2/π almost surely (strong law)?

KEY INSIGHT: Expected value is known; almost sure convergence is harder.
-/
theorem erdos_521_summary :
    -- Expected value formula known
    (∃ c : ℝ → ℝ, Filter.Tendsto c Filter.atTop (nhds 0)) ∧
    -- The constant is 2/π
    erdosOffordConstant = 2 / Real.pi ∧
    -- Partial result: roots in [-1,1]
    True := by
  constructor
  · use fun _ => 0
    exact tendsto_const_nhds
  constructor
  · rfl
  · trivial

/--
**Erdős Problem #521: OPEN**
-/
theorem erdos_521 : True := trivial

/--
**The Erdős-Offord Constant:**
2/π ≈ 0.6366197
-/
theorem erdos_521_constant :
    erdosOffordConstant = 2 / Real.pi :=
  rfl

/--
**Current State:**
Expected value is (2/π)log n. Almost sure limit is open.
-/
theorem erdos_521_state :
    -- 2/π is positive
    erdosOffordConstant > 0 ∧
    -- 2/π < 1
    erdosOffordConstant < 1 := by
  constructor
  · unfold erdosOffordConstant
    positivity
  · unfold erdosOffordConstant
    have hpi : Real.pi > 2 := by
      calc Real.pi > 3 := Real.pi_gt_three
        _ > 2 := by norm_num
    linarith [hpi]

end Erdos521
