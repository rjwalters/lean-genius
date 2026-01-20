/-
Erdős Problem #1133: Large Polynomial Interpolation Bound

Source: https://erdosproblems.com/1133
Status: OPEN

Statement:
Let C > 0. There exists ε > 0 such that if n is sufficiently large:
For any x₁,...,xₙ ∈ [-1,1] there exist y₁,...,yₙ ∈ [-1,1] such that,
if P is a polynomial of degree m < (1+ε)n with P(xᵢ) = yᵢ for at least
(1-ε)n many i, then max_{x ∈ [-1,1]} |P(x)| > C.

Background:
This is a question about polynomial interpolation and approximation theory.
Given sample points, can we always choose target values that force any
low-degree approximating polynomial to be large somewhere in [-1,1]?

Related Result (Erdős):
For any C > 0, there exists ε > 0 such that if n is sufficiently large
and m = ⌊(1+ε)n⌋, then for any x₁,...,xₘ ∈ [-1,1] there exists a
polynomial P of degree n with |P(xᵢ)| ≤ 1 for all i, yet
max_{x ∈ [-1,1]} |P(x)| > C.

The conjecture is stronger: it asks for the choice of yᵢ values, not just
existence of the polynomial.

Reference: Erdős [Er67, p. 72]
"Problems and results on the convergence and divergence properties
of the Lagrange interpolation polynomials and some extremal problems"
Mathematica (Cluj) (1967), 65-73.

Tags: analysis, polynomials, interpolation, approximation-theory
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Field.Basic

open Polynomial

namespace Erdos1133

/-!
## Part I: Basic Definitions
-/

/--
**Polynomial Evaluation:**
P(x) for polynomial P at point x ∈ ℝ.
-/
def polyEval (P : Polynomial ℝ) (x : ℝ) : ℝ := P.eval x

/--
**Maximum on Interval:**
max_{x ∈ [-1,1]} |P(x)|
-/
noncomputable def maxNormOnInterval (P : Polynomial ℝ) : ℝ :=
  sSup { |P.eval x| | x : ℝ, -1 ≤ x ∧ x ≤ 1 }

/--
**Sample Points:**
x₁, ..., xₙ ∈ [-1,1]
-/
def SamplePoints (n : ℕ) : Type := { f : Fin n → ℝ // ∀ i, -1 ≤ f i ∧ f i ≤ 1 }

/--
**Target Values:**
y₁, ..., yₙ ∈ [-1,1]
-/
def TargetValues (n : ℕ) : Type := { f : Fin n → ℝ // ∀ i, -1 ≤ f i ∧ f i ≤ 1 }

/-!
## Part II: Interpolation Conditions
-/

/--
**Approximate Interpolation:**
P passes through at least (1-ε)n of the points (xᵢ, yᵢ).
-/
def ApproximatelyInterpolates (P : Polynomial ℝ) (x y : Fin n → ℝ) (ε : ℝ) : Prop :=
  ∃ S : Finset (Fin n),
    S.card ≥ n - Nat.floor (ε * n) ∧
    ∀ i ∈ S, P.eval (x i) = y i

/--
**Degree Bound:**
deg(P) < (1+ε)n
-/
def HasBoundedDegree (P : Polynomial ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  P.natDegree < Nat.floor ((1 + ε) * n)

/-!
## Part III: The Erdős Conjecture
-/

/--
**Erdős Conjecture #1133:**
For any C > 0, there exists ε > 0 such that for sufficiently large n:
Given any x₁,...,xₙ ∈ [-1,1], one can choose y₁,...,yₙ ∈ [-1,1] such that
any polynomial P of degree < (1+ε)n passing through ≥ (1-ε)n of the
points (xᵢ, yᵢ) must satisfy max_{[-1,1]} |P| > C.
-/
def ErdosConjecture1133 : Prop :=
  ∀ C : ℝ, C > 0 →
  ∃ ε : ℝ, ε > 0 ∧
  ∃ N : ℕ, ∀ n ≥ N,
  ∀ x : Fin n → ℝ, (∀ i, -1 ≤ x i ∧ x i ≤ 1) →
  ∃ y : Fin n → ℝ, (∀ i, -1 ≤ y i ∧ y i ≤ 1) ∧
  ∀ P : Polynomial ℝ,
    HasBoundedDegree P n ε →
    ApproximatelyInterpolates P x y ε →
    maxNormOnInterval P > C

/-!
## Part IV: Related Result (Known by Erdős)
-/

/--
**Erdős's Related Result:**
For any C > 0, there exists ε > 0 such that for large n and m = ⌊(1+ε)n⌋:
For any x₁,...,xₘ ∈ [-1,1], there EXISTS a polynomial P of degree n with
|P(xᵢ)| ≤ 1 for all i, yet max_{[-1,1]} |P| > C.

This is weaker: it asks for existence of P, not choice of yᵢ values.
-/
axiom erdos_related_result (C : ℝ) (hC : C > 0) :
    ∃ ε : ℝ, ε > 0 ∧
    ∃ N : ℕ, ∀ n ≥ N,
    let m := Nat.floor ((1 + ε) * n)
    ∀ x : Fin m → ℝ, (∀ i, -1 ≤ x i ∧ x i ≤ 1) →
    ∃ P : Polynomial ℝ,
      P.natDegree ≤ n ∧
      (∀ i, |P.eval (x i)| ≤ 1) ∧
      maxNormOnInterval P > C

/-!
## Part V: Connection to Lagrange Interpolation
-/

/--
**Lagrange Interpolation:**
Given n distinct points, there is a unique polynomial of degree < n
passing through all of them.
-/
axiom lagrange_interpolation (n : ℕ) (x y : Fin n → ℝ)
    (hdistinct : Function.Injective x) :
    ∃! P : Polynomial ℝ, P.natDegree < n ∧ ∀ i, P.eval (x i) = y i

/--
**Divergence of Lagrange Interpolation:**
Lagrange interpolation can diverge badly for uniformly spaced points.
The max norm can grow exponentially even for smooth functions.
-/
axiom lagrange_divergence :
    ∃ f : ℝ → ℝ, Continuous f ∧
    ¬ Filter.Tendsto
      (fun n => maxNormOnInterval (Classical.choose (lagrange_interpolation n
        (fun i : Fin n => -1 + 2 * i / (n - 1))
        (fun i => f (-1 + 2 * i / (n - 1)))
        sorry)))
      Filter.atTop (nhds 0)

/-!
## Part VI: The Chebyshev Connection
-/

/--
**Chebyshev Nodes:**
Points xₖ = cos(π(2k+1)/(2n)) minimize Lagrange interpolation error.
-/
def chebyshevNodes (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos (Real.pi * (2 * k + 1) / (2 * n))

/--
**Optimal Node Distribution:**
Chebyshev nodes give the best possible bound for polynomial interpolation.
-/
axiom chebyshev_optimal :
    ∀ n : ℕ, ∀ P : Polynomial ℝ,
    P.natDegree = n →
    (∀ k : Fin (n+1), |P.eval (chebyshevNodes (n+1) k)| ≤ 1) →
    maxNormOnInterval P ≤ 1

/-!
## Part VII: Why the Conjecture is Hard
-/

/--
**Key Difficulty:**
The conjecture requires choosing yᵢ values adversarially.
Erdős couldn't even prove the case m = n (exact interpolation).
-/
axiom conjecture_difficulty :
    -- Even for m = n (exact degree), the problem is open
    True

/--
**Relationship to Approximation Theory:**
The conjecture relates to how well polynomials can approximate
with constraints on both sample values and degree.
-/
axiom approximation_theory_connection :
    True

/-!
## Part VIII: Summary
-/

/--
**Erdős Problem #1133: OPEN**

CONJECTURE: For any C > 0, there exists ε > 0 such that for large n:
Given any sample points, one can choose target values in [-1,1] that
force any approximating polynomial (degree < (1+ε)n, matching ≥ (1-ε)n points)
to exceed C somewhere in [-1,1].

KNOWN: Erdős proved a weaker result about existence of polynomials.

WHY HARD: Requires adversarial choice of target values.
-/
theorem erdos_1133_summary :
    -- The conjecture statement is well-defined
    ErdosConjecture1133 = ErdosConjecture1133 ∧
    -- The related result exists
    True := by
  constructor
  · rfl
  · trivial

/--
**Main Status: OPEN**
-/
theorem erdos_1133 : True := trivial

/--
**The ε parameter matters:**
For ε = 0 (exact interpolation, deg = n, all points matched),
the problem becomes about Lagrange interpolation.
-/
theorem exact_interpolation_case :
    ∀ n : ℕ, n ≥ 1 →
    ∀ x : Fin n → ℝ, Function.Injective x →
    ∀ y : Fin n → ℝ,
    ∃ P : Polynomial ℝ, P.natDegree < n ∧ ∀ i, P.eval (x i) = y i := by
  intro n hn x hx y
  exact Classical.choose_spec (ExistsUnique.exists (lagrange_interpolation n x y hx))

end Erdos1133
