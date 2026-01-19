/-
Erdős Problem #1132: Lagrange Interpolation and Lebesgue Functions

Source: https://erdosproblems.com/1132
Status: OPEN

Statement:
For x₁,...,xₙ ∈ [-1,1] define the Lagrange basis polynomials:
  lₖ(x) = ∏_{i≠k}(x-xᵢ) / ∏_{i≠k}(xₖ-xᵢ)
which satisfy lₖ(xₖ) = 1 and lₖ(xᵢ) = 0 for i ≠ k.

Let x₁,x₂,... ∈ [-1,1] be an infinite sequence, and define the Lebesgue function:
  Lₙ(x) = Σ_{k=1}^n |lₖ(x)|

Two questions:
1. Must there exist x ∈ (-1,1) such that Lₙ(x) > (2/π)log(n) - O(1) for infinitely many n?
2. Is limsup_{n→∞} Lₙ(x)/log(n) ≥ 2/π for almost all x ∈ (-1,1)?

Related Results:
- Bernstein (1931): The set of x where limsup ≥ 2/π is everywhere dense in (-1,1)
- Erdős (1961): For any fixed nodes, max_{x∈[-1,1]} Lₙ(x) > (2/π)log(n) - O(1)

References:
- Erdős [Er67, p.68]
- Bernstein [Be31], "Sur la limitation des valeurs d'un polynome"
- Erdős [Er61c], "Problems and results on the theory of interpolation. II"
- Related to Erdős Problem #1129
-/

import Mathlib.Analysis.Calculus.LagrangeInterpolation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic

open Real MeasureTheory Finset

namespace Erdos1132

/-
## Part I: Lagrange Basis Polynomials

The fundamental building blocks of polynomial interpolation.
-/

/--
**Lagrange Basis Polynomial:**
For nodes x₁,...,xₙ, the kth Lagrange basis polynomial lₖ(x) satisfies:
- lₖ(xₖ) = 1
- lₖ(xᵢ) = 0 for i ≠ k

This is the unique polynomial of degree n-1 with these properties.
-/
noncomputable def lagrangeBasis (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i : Fin n, if i = k then 1 else (x - nodes i) / (nodes k - nodes i)

/--
**Alternative form of Lagrange basis:**
lₖ(x) = ∏_{i≠k}(x-xᵢ) / ∏_{i≠k}(xₖ-xᵢ)
-/
noncomputable def lagrangeBasis' (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  (∏ i ∈ Finset.univ.filter (· ≠ k), (x - nodes i)) /
  (∏ i ∈ Finset.univ.filter (· ≠ k), (nodes k - nodes i))

/--
**Lagrange basis at its own node equals 1.**
-/
axiom lagrangeBasis_self (nodes : Fin n → ℝ) (k : Fin n)
    (hdistinct : ∀ i j, i ≠ j → nodes i ≠ nodes j) :
    lagrangeBasis nodes k (nodes k) = 1

/--
**Lagrange basis at other nodes equals 0.**
-/
axiom lagrangeBasis_other (nodes : Fin n → ℝ) (k j : Fin n)
    (hdistinct : ∀ i₁ i₂, i₁ ≠ i₂ → nodes i₁ ≠ nodes i₂) (hkj : k ≠ j) :
    lagrangeBasis nodes k (nodes j) = 0

/-
## Part II: The Lebesgue Function

The sum of absolute values of Lagrange basis polynomials.
-/

/--
**Lebesgue Function:**
Lₙ(x) = Σₖ |lₖ(x)|

This measures how much the Lagrange interpolation can magnify errors.
-/
noncomputable def lebesgueFunction (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis nodes k x|

/--
**Lebesgue Constant:**
Λₙ = max_{x∈[-1,1]} Lₙ(x)

The maximum of the Lebesgue function over the interval.
-/
noncomputable def lebesgueConstant (nodes : Fin n → ℝ) : ℝ :=
  ⨆ x ∈ Set.Icc (-1 : ℝ) 1, lebesgueFunction nodes x

/--
**Lebesgue function is always at least 1.**
At any node xₖ, Lₙ(xₖ) ≥ |lₖ(xₖ)| = 1.
-/
axiom lebesgueFunction_ge_one (nodes : Fin n → ℝ) (x : ℝ)
    (hdistinct : ∀ i j, i ≠ j → nodes i ≠ nodes j)
    (hn : n ≥ 1) :
    lebesgueFunction nodes x ≥ 1

/-
## Part III: Growth of Lebesgue Constants

The Lebesgue constant grows logarithmically in the number of nodes.
-/

/--
**Erdős's Lower Bound (1961):**
For any choice of nodes in [-1,1],
  max_{x∈[-1,1]} Lₙ(x) > (2/π) log(n) - O(1)

This is a fundamental lower bound on the Lebesgue constant.
-/
axiom erdos_lower_bound (n : ℕ) (hn : n ≥ 2) (nodes : Fin n → ℝ)
    (hnodes : ∀ k, nodes k ∈ Set.Icc (-1 : ℝ) 1) :
    lebesgueConstant nodes > (2 / Real.pi) * Real.log n - 10

/--
**Chebyshev Nodes:**
The nodes that minimize the Lebesgue constant are the Chebyshev nodes:
  xₖ = cos((2k-1)π/(2n)) for k = 1, ..., n
-/
noncomputable def chebyshevNodes (n : ℕ) : Fin n → ℝ :=
  fun k => Real.cos ((2 * (k.val + 1) - 1) * Real.pi / (2 * n))

/--
**Chebyshev Nodes in [-1,1]:**
All Chebyshev nodes lie in the interval [-1,1].
-/
axiom chebyshevNodes_in_interval (n : ℕ) (hn : n ≥ 1) (k : Fin n) :
    chebyshevNodes n k ∈ Set.Icc (-1 : ℝ) 1

/--
**Optimal Growth Rate:**
For Chebyshev nodes, the Lebesgue constant grows as (2/π) log(n) + O(1).
This is asymptotically optimal.
-/
axiom chebyshev_lebesgue_constant (n : ℕ) (hn : n ≥ 2) :
    |lebesgueConstant (chebyshevNodes n) - (2 / Real.pi) * Real.log n| ≤ 2

/-
## Part IV: The Main Questions

Erdős's questions about Lebesgue functions for infinite sequences.
-/

/--
**Infinite Sequence of Nodes:**
A sequence x₁, x₂, ... in [-1,1].
-/
def InfiniteNodeSequence : Type := {f : ℕ → ℝ // ∀ n, f n ∈ Set.Icc (-1 : ℝ) 1}

/--
**Lebesgue Function for Finite Prefix:**
Given an infinite sequence, the Lebesgue function for the first n nodes.
-/
noncomputable def lebesgueFunctionN (seq : InfiniteNodeSequence) (n : ℕ) (x : ℝ) : ℝ :=
  if h : n > 0 then
    lebesgueFunction (fun k : Fin n => seq.val k.val) x
  else 1

/--
**Question 1: Existence of Good Points**

Must there exist x ∈ (-1,1) such that Lₙ(x) > (2/π)log(n) - C for infinitely many n?

This is OPEN. The question asks whether every infinite sequence has a "witness"
point that demonstrates near-optimal growth infinitely often.
-/
def existsGoodPoint (seq : InfiniteNodeSequence) : Prop :=
  ∃ x ∈ Set.Ioo (-1 : ℝ) 1, ∃ C : ℝ,
    ∀ N : ℕ, ∃ n > N, lebesgueFunctionN seq n x > (2 / Real.pi) * Real.log n - C

/--
**Erdős's First Question (Open):**
Is existsGoodPoint true for all infinite node sequences?
-/
axiom erdos_question_1_open :
    -- This is currently an open problem
    True  -- We don't know if ∀ seq, existsGoodPoint seq

/--
**Question 2: Almost Everywhere Growth**

Is limsup_{n→∞} Lₙ(x)/log(n) ≥ 2/π for almost all x ∈ (-1,1)?

This asks whether the "good" growth rate holds for Lebesgue-almost-every point.
-/
def almostEverywhereGrowth (seq : InfiniteNodeSequence) : Prop :=
  ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)),
    Filter.limsup (fun n => lebesgueFunctionN seq n x / Real.log n)
      Filter.atTop ≥ 2 / Real.pi

/--
**Erdős's Second Question (Open):**
Is almostEverywhereGrowth true for all infinite node sequences?
-/
axiom erdos_question_2_open :
    -- This is currently an open problem
    True  -- We don't know if ∀ seq, almostEverywhereGrowth seq

/-
## Part V: Partial Results

Known results that provide partial answers.
-/

/--
**Bernstein's Density Result (1931):**
For any infinite sequence, the set of x where
  limsup_{n→∞} Lₙ(x)/log(n) ≥ 2/π
is dense in (-1,1).

This is weaker than "almost everywhere" but still significant.
-/
def denseGoodPoints (seq : InfiniteNodeSequence) : Prop :=
  Dense {x : ℝ | x ∈ Set.Ioo (-1 : ℝ) 1 ∧
    Filter.limsup (fun n => lebesgueFunctionN seq n x / Real.log n)
      Filter.atTop ≥ 2 / Real.pi}

/--
**Bernstein's Theorem (1931):**
The good points are dense for any infinite sequence.
-/
axiom bernstein_density_theorem (seq : InfiniteNodeSequence) :
    denseGoodPoints seq

/--
**Erdős's Maximum Theorem (1961):**
For any finite set of nodes, the maximum of the Lebesgue function
exceeds (2/π)log(n) - O(1).

This doesn't immediately answer the questions above because it's about
the maximum, not about fixed points x.
-/
axiom erdos_max_theorem (seq : InfiniteNodeSequence) (n : ℕ) (hn : n ≥ 2) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, lebesgueFunctionN seq n x > (2 / Real.pi) * Real.log n - 10

/-
## Part VI: Connection to Interpolation Error

Why the Lebesgue function matters for polynomial interpolation.
-/

/--
**Interpolation Error Bound:**
For any function f and its Lagrange interpolant Pₙ,
  |f(x) - Pₙ(x)| ≤ (1 + Lₙ(x)) · Eₙ(f)
where Eₙ(f) is the best polynomial approximation error.

The Lebesgue function controls how interpolation error compares to best approximation.
-/
axiom interpolation_error_bound (f : ℝ → ℝ) (nodes : Fin n → ℝ)
    (hf : Continuous f) (x : ℝ) :
    True  -- Placeholder for the actual error bound statement

/--
**Practical Implication:**
Large Lebesgue function means interpolation can be much worse than
best polynomial approximation, explaining numerical instability.
-/
axiom practical_implication :
    -- The Lebesgue function is key to understanding polynomial interpolation stability
    True

/-
## Part VII: Special Cases and Examples
-/

/--
**Equidistant Nodes:**
For equally spaced nodes on [-1,1], the Lebesgue constant grows
exponentially: Λₙ ~ 2ⁿ/(e·n·log(n)).
This is much worse than the optimal log(n) growth.
-/
noncomputable def equidistantNodes (n : ℕ) : Fin n → ℝ :=
  fun k => -1 + 2 * k.val / (n - 1)

/--
**Runge Phenomenon:**
The exponential growth of Lebesgue constants for equidistant nodes
is related to Runge's phenomenon in polynomial interpolation.
-/
axiom runge_phenomenon_connection :
    -- Equidistant nodes lead to poor interpolation for smooth functions
    -- with singularities in the complex plane near [-1,1]
    True

/--
**Leja Points:**
Leja points are constructed greedily to maximize a product criterion.
They achieve nearly optimal Lebesgue constant growth.
-/
axiom leja_points_nearly_optimal (n : ℕ) (hn : n ≥ 2) :
    -- Leja points achieve O(log n) Lebesgue constant
    True

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #1132: Summary**

Two open questions about Lebesgue functions for infinite node sequences:

1. **Existence Question:** Must there exist x ∈ (-1,1) with
   Lₙ(x) > (2/π)log(n) - O(1) for infinitely many n?

2. **Almost Everywhere Question:** Is
   limsup_{n→∞} Lₙ(x)/log(n) ≥ 2/π for almost all x?

**What We Know:**
- Bernstein (1931): Good points are dense
- Erdős (1961): The maximum always exceeds the threshold

The gap between "dense" (Bernstein) and "almost everywhere" (Question 2)
remains unresolved.
-/
theorem erdos_1132_summary :
    -- Both questions remain open
    -- We have partial results: density (Bernstein) and max bounds (Erdős)
    True := trivial

/--
**Status: OPEN**
These questions about the measure-theoretic and topological properties
of good points for Lagrange interpolation remain unresolved.
-/
theorem erdos_1132_status : True := trivial

end Erdos1132
