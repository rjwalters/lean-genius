/-
Erdős Problem #1117: Maximum Modulus Points of Entire Functions

**Statement**: Let f(z) be an entire function which is not a monomial.
Let ν(r) count the number of z with |z|=r such that |f(z)| = max_{|z|=r} |f(z)|.
(This is finite if f is not a monomial.)

Question 1: Is limsup ν(r) = ∞ possible?
Question 2: Is liminf ν(r) = ∞ possible?

**Answer**:
- Q1: YES - proved by Herzog & Piranian (1968)
- Q2: OPEN - approximate answer by Glücksam & Pardo-Simón (2024)

**Historical Development**:
- Hayman (1974): Problem 2.16 in "Research Problems in Function Theory"
- Herzog-Piranian (1968): Proved Q1 by construction
- Glücksam-Pardo-Simón (2024): Approximate affirmative for Q2

**Mathematical Context**:
For a non-constant entire function, the maximum modulus on each circle |z| = r
is attained at finitely many points (except for monomials cz^n where it's
attained everywhere). This problem asks about the behavior of this count as r → ∞.

Reference: https://erdosproblems.com/1117
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Finite.Basic

open scoped Nat
open Filter Real Set Topology

namespace Erdos1117

/-
## Basic Definitions
-/

/-- An entire function: holomorphic on all of ℂ. -/
def IsEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

/-- A monomial function: f(z) = c * z^n for some c ∈ ℂ, n ∈ ℕ. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (n : ℕ), ∀ z : ℂ, f z = c * z ^ n

/-- The circle of radius r in ℂ. -/
def circle (r : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ = r}

/-- The maximum modulus M(r) = max_{|z|=r} |f(z)|. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- The set of points on |z|=r where |f(z)| achieves the maximum. -/
def maxModulusPoints (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ = r ∧ ‖f z‖ = maxModulus f r}

/-- ν(r): the count of maximum modulus points on the circle |z| = r.
    This is defined as the cardinality of the set of such points.
    For non-monomials, this is always finite. -/
noncomputable def nu (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  (maxModulusPoints f r).ncard

/-
## Key Structural Results
-/

/-- For a non-monomial entire function, ν(r) is finite for all r > 0.
    This follows from the maximum modulus principle: if |f| is constant
    on a circle, then f is a monomial (or constant). -/
theorem nu_finite_of_not_monomial (f : ℂ → ℂ)
    (hf : IsEntire f) (hnm : ¬IsMonomial f) (r : ℝ) (hr : r > 0) :
    (maxModulusPoints f r).Finite := by
  sorry

/-- A monomial has ν(r) = ∞ (every point on the circle achieves max). -/
theorem monomial_nu_infinite (c : ℂ) (n : ℕ) (r : ℝ) (hr : r > 0) (hc : c ≠ 0) :
    (maxModulusPoints (fun z => c * z ^ n) r).Infinite := by
  sorry

/-
## Question 1: limsup ν(r) = ∞

Herzog and Piranian (1968) showed this is possible by constructing
an explicit entire function where ν(r) → ∞ along a subsequence.
-/

/-- Statement: limsup ν(r) = ∞ is achievable.
    There exists an entire non-monomial function with limsup ν(r) = ∞. -/
def Q1_limsup_infinite : Prop :=
  ∃ f : ℂ → ℂ,
    IsEntire f ∧
    ¬IsMonomial f ∧
    limsup (fun r : ℝ => (nu f r : ℝ)) atTop = ⊤

/-- Herzog-Piranian Theorem (1968): Q1 has an affirmative answer.
    They constructed an entire function with arbitrarily large ν(r).

    The construction uses a lacunary series with carefully chosen
    coefficients that create interference patterns, causing the
    maximum to be achieved at increasingly many points for certain radii.

    Axiomatized as the full proof requires construction techniques
    beyond current Mathlib capabilities. -/
axiom herzog_piranian_theorem : Q1_limsup_infinite

/-- Erdős Problem #1117 Question 1 is SOLVED: The answer is YES. -/
theorem erdos_1117_q1_solved : Q1_limsup_infinite :=
  herzog_piranian_theorem

/-
## Question 2: liminf ν(r) = ∞

This question remains OPEN. The question is whether there exists
an entire non-monomial function where ν(r) ≥ N for ALL large r,
for any fixed N.
-/

/-- Statement: liminf ν(r) = ∞ is achievable.
    There exists an entire non-monomial function where
    for any N, we have ν(r) ≥ N for all sufficiently large r. -/
def Q2_liminf_infinite : Prop :=
  ∃ f : ℂ → ℂ,
    IsEntire f ∧
    ¬IsMonomial f ∧
    ∀ N : ℕ, ∃ R : ℝ, ∀ r : ℝ, r ≥ R → nu f r ≥ N

/-- An 'approximate' version proved by Glücksam and Pardo-Simón (2024).
    They showed a weaker result where the count is allowed to dip
    occasionally but tends to infinity in a suitable sense.

    The precise statement involves logarithmic density conditions. -/
def Q2_approximate_solution : Prop :=
  ∃ f : ℂ → ℂ,
    IsEntire f ∧
    ¬IsMonomial f ∧
    -- For any N, the set of r where ν(r) < N has logarithmic density 0
    ∀ N : ℕ, Tendsto
      (fun R => (∫ r in (1)..R, if nu f r < N then 1 / r else 0) / Real.log R)
      atTop (nhds 0)

/-- Glücksam-Pardo-Simón (2024): An approximate affirmative answer to Q2. -/
axiom glucksam_pardo_simon_theorem : Q2_approximate_solution

/-- Q2 proper remains OPEN. This is a conjecture, not a theorem. -/
def erdos_1117_q2_conjecture : Prop := Q2_liminf_infinite

/-
## Related Results
-/

/-- Lower bound: For any entire non-monomial function, ν(r) ≥ 1 for all r > 0.
    The maximum is always achieved somewhere! -/
theorem nu_ge_one (f : ℂ → ℂ)
    (hf : IsEntire f) (hnm : ¬IsMonomial f) (r : ℝ) (hr : r > 0) :
    nu f r ≥ 1 := by
  sorry

/-- For polynomials of degree n, we have ν(r) ≤ n for large r.
    This follows from the argument principle applied to f'(z)/f(z). -/
theorem polynomial_nu_bounded (f : ℂ → ℂ) (n : ℕ)
    (hf : ∃ (coeffs : Fin (n + 1) → ℂ),
      ∀ z, f z = ∑ i : Fin (n + 1), coeffs i * z ^ (i : ℕ))
    (hn : n ≥ 1) :
    ∃ R : ℝ, ∀ r : ℝ, r ≥ R → nu f r ≤ n := by
  sorry

/-
## Summary

**Erdős Problem #1117**:
- Q1 (limsup ν(r) = ∞?): SOLVED - YES (Herzog-Piranian 1968)
- Q2 (liminf ν(r) = ∞?): OPEN (approximate solution: Glücksam-Pardo-Simón 2024)

The key insight is that while we can construct functions with
arbitrarily large ν(r) along subsequences (Q1), ensuring ν(r)
stays large for ALL large r (Q2) is much harder. The approximate
solution shows this is "almost" achievable in the sense of logarithmic density.
-/

end Erdos1117
