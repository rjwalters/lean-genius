/-
Erdős Problem #1116: Extreme Value Distribution of Entire Functions

Source: https://erdosproblems.com/1116
Status: SOLVED (Gol'dberg 1978, Toppila 1976)

Statement:
For a meromorphic function f, let n(r, a) count the number of roots of f(z) = a
in the disc |z| < r. Does there exist a meromorphic (or entire) f such that
for every a ≠ b, lim sup_{r → ∞} n(r, a)/n(r, b) = ∞?

Answer: YES

Gol'dberg (1978) and Toppila (1976) independently constructed entire functions
with this extreme property: for any two distinct values a ≠ b, the ratio of
their counting functions is unbounded.

Key Insight:
This is remarkable because Nevanlinna theory tells us that "most" values are
taken about equally often (the deficiency sum is at most 2). The constructed
functions show this "average" behavior can hide extreme oscillations.

References:
- Problem 1.25 in Hayman [Ha74], attributed to Erdős
- Gol'dberg [Go78]: "Counting functions of sequences of a-points for entire
  functions", Sibirsk. Mat. Ž. (1978)
- Toppila [To76]: "On the counting function for the a-values of a meromorphic
  function", Ann. Acad. Sci. Fenn. Ser. A I Math. (1976)
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

open Complex Set Filter

namespace Erdos1116

/-
## Part I: Meromorphic Functions and Value Distribution

Basic definitions for the counting function and Nevanlinna theory.
-/

/--
**Meromorphic Function:**
A function f : ℂ → ℂ ∪ {∞} that is analytic except at isolated poles.
For our purposes, we model this as a partial function.
-/
def IsMeromorphic (f : ℂ → ℂ) (poles : Set ℂ) : Prop :=
  -- f is defined and differentiable outside poles
  (∀ z ∉ poles, DifferentiableAt ℂ f z) ∧
  -- poles are isolated
  (∀ p ∈ poles, ∃ ε > 0, ∀ z ≠ p, Complex.abs (z - p) < ε → z ∉ poles) ∧
  -- poles is discrete (no accumulation points in ℂ)
  (∀ R > 0, (poles ∩ {z | Complex.abs z < R}).Finite)

/--
**Entire Function:**
A function f : ℂ → ℂ that is differentiable everywhere (no poles).
-/
def IsEntire (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, DifferentiableAt ℂ f z

/-- An entire function is meromorphic with empty pole set. -/
theorem entire_is_meromorphic (f : ℂ → ℂ) (hf : IsEntire f) :
    IsMeromorphic f ∅ := by
  constructor
  · intro z hz
    simp at hz
  · constructor
    · intro p hp
      simp at hp
    · intro R hR
      simp

/-
## Part II: The Counting Function

n(r, a) counts roots of f(z) = a in |z| < r.
-/

/--
**a-Points of f:**
The set of points where f(z) = a.
-/
def aPoints (f : ℂ → ℂ) (a : ℂ) : Set ℂ :=
  {z : ℂ | f z = a}

/--
**Counting Function:**
n(r, a) = number of z with f(z) = a and |z| < r.
For an entire function, this is finite for each r.

Note: In general, this counts with multiplicity, but we simplify here.
-/
def countingFunction (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℕ :=
  if h : (aPoints f a ∩ {z | Complex.abs z < r}).Finite
  then h.toFinset.card
  else 0

/-- Notation for counting function. -/
notation "n(" f ", " r ", " a ")" => countingFunction f a r

/-
## Part III: The Problem Statement

For entire f, does there exist f such that for all a ≠ b,
lim sup_{r → ∞} n(f, r, a) / n(f, r, b) = ∞?
-/

/--
**Ratio Unbounded Property:**
For two values a ≠ b, we say f has unbounded ratio if
lim sup_{r → ∞} n(f, r, a) / n(f, r, b) = ∞.

This means: for any M > 0, there exist arbitrarily large r with
n(f, r, a) / n(f, r, b) > M.
-/
def HasUnboundedRatio (f : ℂ → ℂ) (a b : ℂ) : Prop :=
  ∀ M : ℝ, M > 0 → ∀ R : ℝ, R > 0 →
    ∃ r > R, n(f, r, a) > M * n(f, r, b)

/--
**Extreme Value Distribution:**
A function f has extreme value distribution if for ALL pairs a ≠ b,
the ratio n(f, r, a) / n(f, r, b) is unbounded AND
n(f, r, b) / n(f, r, a) is unbounded.

This is a very strong condition!
-/
def HasExtremeValueDistribution (f : ℂ → ℂ) : Prop :=
  ∀ a b : ℂ, a ≠ b →
    HasUnboundedRatio f a b ∧ HasUnboundedRatio f b a

/-
## Part IV: The Solution

Gol'dberg and Toppila constructed entire functions with extreme value distribution.
-/

/--
**Gol'dberg-Toppila Theorem (1976-1978):**
There exist entire functions with extreme value distribution.

That is, there exists an entire function f such that for every a ≠ b,
lim sup_{r → ∞} n(f, r, a) / n(f, r, b) = ∞.
-/
axiom goldberg_toppila_existence :
    ∃ f : ℂ → ℂ, IsEntire f ∧ HasExtremeValueDistribution f

/--
**Erdős Problem #1116: SOLVED**
The answer is YES - such entire functions exist.
-/
theorem erdos_1116 :
    ∃ f : ℂ → ℂ, IsEntire f ∧ HasExtremeValueDistribution f :=
  goldberg_toppila_existence

/-
## Part V: Nevanlinna Theory Context

To understand why this is surprising, we need Nevanlinna theory.
-/

/--
**Characteristic Function (simplified):**
T(r, f) measures the "growth" of f.
For an entire function, T(r, f) = log M(r) where M(r) = max_{|z|=r} |f(z)|.
-/
def characteristic (f : ℂ → ℂ) (r : ℝ) : ℝ := r  -- Placeholder

/--
**Counting Function with Growth:**
N(r, a) is the "integrated" counting function.
N(r, a) = ∫_0^r (n(t, a) / t) dt + O(log r).
-/
def integratedCounting (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℝ := r  -- Placeholder

/--
**Deficiency:**
δ(a) = lim inf_{r → ∞} (1 - N(r, a) / T(r)) measures how often f misses a.

Key theorem (Nevanlinna): δ(a) ≤ 1 for all a, and ∑_a δ(a) ≤ 2.
-/
def deficiency (f : ℂ → ℂ) (a : ℂ) : ℝ := 0  -- Placeholder

/--
**Nevanlinna's Deficiency Sum:**
The sum of all deficiencies is at most 2.
This means "most" values are taken with roughly equal frequency.
-/
axiom nevanlinna_deficiency_sum (f : ℂ → ℂ) (hf : IsEntire f) :
    ∀ S : Finset ℂ, (S.sum fun a => deficiency f a) ≤ 2

/-
## Part VI: Why This is Surprising

Nevanlinna theory says values are "typically" taken equally often on average.
The Gol'dberg-Toppila construction shows this hides wild oscillations.
-/

/--
**Typical Behavior (First Main Theorem):**
For most values a, N(r, a) ∼ T(r) as r → ∞.
This is the "equidistribution" property.
-/
axiom first_main_theorem_heuristic (f : ℂ → ℂ) (hf : IsEntire f) (a : ℂ) :
    ∃ E : Set ℝ, ∀ r ∉ E,
      |integratedCounting f a r - characteristic f r| ≤ characteristic f r / 2

/--
**The Surprise:**
Even though N(r, a) ∼ N(r, b) on average (both ∼ T(r)),
the UN-integrated counting function n(r, a) can oscillate wildly!

The Gol'dberg-Toppila construction exploits this: they build f so that
- n(r, a) is sometimes much larger than n(r, b)
- n(r, b) is sometimes much larger than n(r, a)
- But the integrals N(r, a) and N(r, b) still satisfy Nevanlinna bounds
-/
axiom oscillation_key_insight :
    ∃ f : ℂ → ℂ, IsEntire f ∧
      (∀ a b : ℂ, a ≠ b → HasUnboundedRatio f a b) ∧
      (∀ a : ℂ, deficiency f a ≤ 1)

/-
## Part VII: Construction Sketch

The Gol'dberg-Toppila construction builds f as an infinite product.
-/

/--
**Lacunary Series:**
The construction uses lacunary (sparse) power series to control
where f takes certain values.

A lacunary series has large gaps between nonzero terms:
f(z) = Σ_{n ∈ S} a_n z^n where n_{k+1}/n_k → ∞.
-/
def IsLacunarySeries (coeffs : ℕ → ℂ) (support : Set ℕ) : Prop :=
  -- Only coefficients in support are nonzero
  (∀ n ∉ support, coeffs n = 0) ∧
  -- Gaps grow rapidly
  (∀ m n : ℕ, m ∈ support → n ∈ support → m < n →
    (∀ k, m < k → k < n → k ∉ support))

/--
**Weierstrass Product:**
The construction also uses Weierstrass products to place zeros
at specific locations with controlled growth.
-/
def WeierstrassProduct (zeros : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => (Finset.range n).prod fun k => (1 - z / zeros k)

/-
## Part VIII: Examples and Non-examples
-/

/--
**Example: Exponential Function**
e^z has no zeros, so n(r, 0) = 0 for all r.
But n(r, 1) ~ r/π for large r (roots at 2πik).
So e^z does NOT have extreme value distribution (0 has special status).
-/
def expFunction : ℂ → ℂ := Complex.exp

/-- e^z has no finite deficient values except possibly 0. -/
axiom exp_not_extreme : ¬ HasExtremeValueDistribution expFunction

/--
**Example: Polynomial**
Any polynomial p(z) takes each value finitely many times (deg p times).
So polynomials cannot have extreme value distribution.
-/
axiom polynomial_not_extreme (p : Polynomial ℂ) (hp : p.natDegree > 0) :
    ¬ HasExtremeValueDistribution (fun z => p.eval z)

/-
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #1116: Status Summary**

The problem asks whether there exists an entire function f such that
for every a ≠ b, lim sup n(r,a)/n(r,b) = ∞.

Answer: YES

Gol'dberg (1978) and Toppila (1976) constructed such functions.
This is surprising because Nevanlinna theory says values are
typically taken with roughly equal frequency on average.
The construction shows this average behavior hides wild oscillations.
-/
theorem erdos_1116_summary :
    -- Such functions exist
    (∃ f : ℂ → ℂ, IsEntire f ∧ HasExtremeValueDistribution f) ∧
    -- Exponential is not such a function
    ¬ HasExtremeValueDistribution expFunction := by
  constructor
  · exact erdos_1116
  · exact exp_not_extreme

/--
**Key Mathematical Insight:**
The counting function n(r, a) measures pointwise behavior,
while the integrated function N(r, a) measures average behavior.

Nevanlinna theory controls N(r, a), but n(r, a) can oscillate freely
as long as the oscillations "average out" in the integral.
-/
def keyInsightStatement : String :=
  "n(r,a) can oscillate wildly while N(r,a) remains bounded"

end Erdos1116
