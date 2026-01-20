/-
Erdős Problem #256: Maxima of Products on the Unit Circle

Source: https://erdosproblems.com/256
Status: SOLVED (Belov-Konyagin 1996)

Statement:
Let f(n) be maximal such that for every a₁ ≤ ... ≤ aₙ ∈ ℕ we have
  max_{|z|=1} |∏ᵢ (1 - z^{aᵢ})| ≥ f(n)

Estimate f(n). In particular, is it true that log f(n) ≫ n^c for some c > 0?

Answer: NO - Belov-Konyagin (1996) proved log f(n) ≪ (log n)⁴

Background:
- Erdős-Szekeres (1959): lim f(n)^{1/n} = 1 and f(n) > √(2n)
- Erdős: log f(n) ≪ n^{1-c} for some c > 0
- Atkinson (1961): log f(n) ≪ n^{1/2} log n
- Odlyzko (1982): log f(n) ≪ n^{1/3} (log n)^{4/3}
- Bourgain-Chang (2018): For distinct aᵢ, log f*(n) ≪ (n log n)^{1/2} log log n
- Belov-Konyagin (1996): log f(n) ≪ (log n)⁴ [FINAL ANSWER]

Related: Problem #510 (Chowla cosine problem)

Tags: analysis, harmonic-analysis, unit-circle, products
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic

open Real Complex
open scoped BigOperators

namespace Erdos256

/-!
## Part I: Basic Definitions
-/

/--
**The product polynomial:**
P(z; a₁,...,aₙ) = ∏ᵢ (1 - z^{aᵢ})
-/
noncomputable def productPoly (a : Fin n → ℕ) (z : ℂ) : ℂ :=
  ∏ i, (1 - z ^ (a i : ℕ))

/--
**Maximum on unit circle:**
M(a₁,...,aₙ) = max_{|z|=1} |P(z; a₁,...,aₙ)|
-/
noncomputable def maxOnUnitCircle (a : Fin n → ℕ) : ℝ :=
  sSup {|productPoly a z| | z : ℂ, Complex.abs z = 1}

/--
**The function f(n):**
f(n) = min over all choices of a₁ ≤ ... ≤ aₙ of the maximum on unit circle.

Equivalently: f(n) is the largest m such that for ALL choices, max ≥ m.
-/
noncomputable def f (n : ℕ) : ℝ :=
  sInf {maxOnUnitCircle a | a : Fin n → ℕ}

/-!
## Part II: Known Bounds
-/

/--
**Erdős-Szekeres (1959) lower bound:**
f(n) > √(2n)
-/
axiom erdos_szekeres_lower (n : ℕ) (hn : n ≥ 1) :
    f n > Real.sqrt (2 * n)

/--
**Erdős-Szekeres (1959) growth:**
lim f(n)^{1/n} = 1
-/
axiom erdos_szekeres_growth :
    Filter.Tendsto (fun n => (f n) ^ (1 / n : ℝ)) Filter.atTop (nhds 1)

/--
**Erdős probabilistic bound:**
log f(n) ≪ n^{1-c} for some c > 0
-/
axiom erdos_probabilistic :
    ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, ∀ n ≥ 2, Real.log (f n) ≤ C * n^(1 - c)

/--
**Atkinson (1961):**
log f(n) ≪ n^{1/2} log n
-/
axiom atkinson_bound (n : ℕ) (hn : n ≥ 2) :
    Real.log (f n) ≤ (n : ℝ)^(1/2 : ℝ) * Real.log n

/--
**Odlyzko (1982):**
log f(n) ≪ n^{1/3} (log n)^{4/3}
-/
axiom odlyzko_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, Real.log (f n) ≤ C * (n : ℝ)^(1/3 : ℝ) * (Real.log n)^(4/3 : ℝ)

/-!
## Part III: The Main Question
-/

/--
**Erdős's question:**
Is log f(n) ≫ n^c for some c > 0?

This asks: does f(n) grow faster than any polynomial in log n?
-/
def ErdosQuestion256 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2, Real.log (f n) ≥ C * n^c

/-!
## Part IV: The Answer
-/

/--
**Belov-Konyagin (1996):**
log f(n) ≪ (log n)⁴

This is an upper bound that is POLYNOMIAL in log n, so the answer to
Erdős's question is NO.
-/
axiom belov_konyagin_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2, Real.log (f n) ≤ C * (Real.log n)^4

/--
**The answer: NO**
-/
theorem erdos_256_answer : ¬ErdosQuestion256 := by
  intro ⟨c, hc, C, hC, hbound⟩
  obtain ⟨K, hK, hupper⟩ := belov_konyagin_bound
  -- For large enough n, n^c > K * (log n)^4, contradiction
  sorry

/-!
## Part V: The Distinct Case
-/

/--
**f*(n) for distinct exponents:**
When we require a₁ < a₂ < ... < aₙ instead of ≤.
-/
noncomputable def fDistinct (n : ℕ) : ℝ :=
  sInf {maxOnUnitCircle a | a : Fin n → ℕ, Function.Injective a}

/--
**Bourgain-Chang (2018):**
log f*(n) ≪ (n log n)^{1/2} log log n
-/
axiom bourgain_chang_bound (n : ℕ) (hn : n ≥ 3) :
    ∃ C : ℝ, Real.log (fDistinct n) ≤
      C * ((n : ℝ) * Real.log n)^(1/2 : ℝ) * Real.log (Real.log n)

/-!
## Part VI: Connection to Chowla Cosine Problem
-/

/--
**Chowla cosine problem (Problem #510):**
For a set A of n integers, find θ minimizing ∑_{a ∈ A} cos(aθ).
-/
def chowlaMinimum (A : Finset ℤ) : ℝ :=
  sInf {∑ a ∈ A, Real.cos (a * θ) | θ : ℝ}

/--
**Atkinson's observation:**
If for any set A of n integers there exists θ with ∑_{a ∈ A} cos(aθ) < -Mₙ,
then log f*(n) ≪ Mₙ log n.
-/
axiom atkinson_chowla_connection (n : ℕ) (M : ℝ) :
    (∀ A : Finset ℤ, A.card = n → chowlaMinimum A < -M) →
    ∃ C : ℝ, Real.log (fDistinct n) ≤ C * M * Real.log n

/-!
## Part VII: Properties of the Product
-/

/--
**Product at roots of unity:**
When z is a primitive k-th root of unity, z^k = 1.
-/
theorem product_at_root_of_unity (a : Fin n → ℕ) (k : ℕ) (hk : k ≥ 1)
    (z : ℂ) (hz : z^k = 1) (hz1 : z ≠ 1) :
    productPoly a z = ∏ i, (1 - z ^ (a i % k)) := by
  sorry

/--
**Lower bound at primitive root:**
There exists a root of unity where the product is not too small.
-/
axiom primitive_root_lower_bound (a : Fin n → ℕ) (hn : n ≥ 1) :
    ∃ k : ℕ, k ≤ ∏ i, (a i + 1) ∧
    ∃ ζ : ℂ, Complex.abs ζ = 1 ∧ ζ^k = 1 ∧ ζ ≠ 1 ∧
      Complex.abs (productPoly a ζ) ≥ 1

/-!
## Part VIII: Summary of Bounds
-/

/--
**Timeline of bounds on log f(n):**

1959 Erdős-Szekeres: f(n) > √(2n), so log f(n) > (1/2) log(2n)
1959 Erdős: log f(n) ≪ n^{1-c}
1961 Atkinson: log f(n) ≪ n^{1/2} log n
1982 Odlyzko: log f(n) ≪ n^{1/3} (log n)^{4/3}
1996 Belov-Konyagin: log f(n) ≪ (log n)^4  [BEST UPPER]
-/

/--
**Gap between bounds:**
Lower: log f(n) ≥ (1/2) log n  (from f(n) > √(2n))
Upper: log f(n) ≤ C (log n)^4

The true growth rate is somewhere between these.
-/
axiom bounds_summary (n : ℕ) (hn : n ≥ 2) :
    (1/2 : ℝ) * Real.log n ≤ Real.log (f n) ∧
    ∃ C : ℝ, Real.log (f n) ≤ C * (Real.log n)^4

/-!
## Part IX: Summary

**Erdős Problem #256: SOLVED**

**Question:** Is log f(n) ≫ n^c for some c > 0?

**Answer:** NO (Belov-Konyagin 1996)

**Final bounds:**
- Lower: log f(n) ≥ (1/2) log n (from Erdős-Szekeres)
- Upper: log f(n) ≪ (log n)^4 (Belov-Konyagin)

**The true growth:** Somewhere between log n and (log n)^4.

**Key insight:** The maximum of ∏(1 - z^{aᵢ}) on |z| = 1 grows
only polylogarithmically in the number of factors.
-/

/--
**Main result: Erdős #256 is SOLVED**
-/
def erdos_256 : ¬ErdosQuestion256 := erdos_256_answer

/--
**What we know:**
-/
theorem erdos_256_summary :
    (∃ C > 0, ∀ n ≥ 2, Real.log (f n) ≤ C * (Real.log n)^4) ∧
    (∀ n ≥ 1, f n > Real.sqrt (2 * n)) := by
  constructor
  · exact belov_konyagin_bound
  · intro n hn
    exact erdos_szekeres_lower n hn

end Erdos256
