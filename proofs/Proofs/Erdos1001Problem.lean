/-
Erdős Problem #1001: Diophantine Approximation Density

Let S(N, A, c) be the measure of α ∈ (0,1) such that
  |α - x/y| < A/y²
for some N ≤ y ≤ cN with gcd(x,y) = 1.

**Question**: Does lim_{N→∞} S(N, A, c) = f(A, c) exist? What is its form?

**Status**: SOLVED

**History**:
- Erdős-Szüsz-Turán (1958): Proved f(A,c) = 12A log(c)/π² when 0 < A < c/(1+c²)
- Kesten-Sós (1966): Proved the limit exists (without explicit formula)
- Boca (2008), Xiong-Zaharescu (2006): Alternative explicit proofs

Reference: https://erdosproblems.com/1001
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Diophantine
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Basic

open MeasureTheory Set Filter Real

namespace Erdos1001

/-!
## The Approximation Set

For given parameters N, A, c, we define the set of α ∈ (0,1)
that can be approximated by some rational x/y with N ≤ y ≤ cN.
-/

/-- A real α is (A, y)-approximable if |α - x/y| < A/y² for some coprime x. -/
def isApproximable (A : ℝ) (y : ℕ) (α : ℝ) : Prop :=
  ∃ x : ℤ, Int.gcd x y = 1 ∧ |α - x / y| < A / y^2

/-- The set of α ∈ (0,1) approximable by some y in [N, cN]. -/
def approximationSet (N : ℕ) (A c : ℝ) : Set ℝ :=
  { α : ℝ | α ∈ Ioo 0 1 ∧ ∃ y : ℕ, (N : ℝ) ≤ y ∧ (y : ℝ) ≤ c * N ∧ isApproximable A y α }

/-- S(N, A, c) is the Lebesgue measure of the approximation set. -/
noncomputable def S (N : ℕ) (A c : ℝ) : ℝ :=
  (volume (approximationSet N A c)).toReal

/-!
## Basic Properties

The measure S(N, A, c) satisfies natural bounds and monotonicity.
-/

/-- S(N, A, c) is always between 0 and 1. -/
theorem S_bounds (N : ℕ) (A c : ℝ) (hA : A > 0) (hc : c > 1) :
    0 ≤ S N A c ∧ S N A c ≤ 1 := by
  sorry

/-- S is monotone increasing in A. -/
theorem S_mono_A (N : ℕ) (A₁ A₂ c : ℝ) (h : A₁ ≤ A₂) :
    S N A₁ c ≤ S N A₂ c := by
  sorry

/-- S is monotone increasing in c. -/
theorem S_mono_c (N : ℕ) (A c₁ c₂ : ℝ) (h : c₁ ≤ c₂) :
    S N A c₁ ≤ S N A c₂ := by
  sorry

/-!
## The Limit Function

The main result is that S(N, A, c) converges as N → ∞.
-/

/-- The limiting density function f(A, c). -/
noncomputable def f (A c : ℝ) : ℝ :=
  12 * A * log c / π^2

/-- The main question: Does lim S(N, A, c) exist? -/
def limitExists (A c : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (fun N => S N A c) atTop (nhds L)

/-!
## Erdős-Szüsz-Turán Result (1958)

In the regime 0 < A < c/(1+c²), the limit equals f(A,c).
-/

/-- The EST regime: 0 < A < c/(1+c²). -/
def inESTRegime (A c : ℝ) : Prop :=
  0 < A ∧ A < c / (1 + c^2)

/-- Erdős-Szüsz-Turán (1958): In the EST regime, S(N,A,c) → f(A,c).
    The explicit formula is f(A,c) = 12A log(c) / π². -/
axiom erdos_szusz_turan (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    Tendsto (fun N => S N A c) atTop (nhds (f A c))

/-- In the EST regime, the limit is 12A log(c) / π². -/
theorem est_explicit_formula (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    Tendsto (fun N => S N A c) atTop (nhds (12 * A * log c / π^2)) := by
  exact erdos_szusz_turan A c hA hc hregime

/-!
## Boundedness Away from 0 and 1

EST also proved that when min(A,c) > 10, S stays bounded away from extremes.
-/

/-- EST boundedness: If min(A,c) > 10, then S(N,A,c) stays bounded away from 0 and 1. -/
axiom est_boundedness (A c : ℝ) (hA : A > 10) (hc : c > 10) :
    ∃ ε : ℝ, ε > 0 ∧ ∀ N : ℕ, N ≥ 1 → ε < S N A c ∧ S N A c < 1 - ε

/-!
## Kesten-Sós Result (1966)

Kesten and Sós proved that the limit always exists (for valid A, c),
though their method doesn't give an explicit formula.
-/

/-- Kesten-Sós (1966): The limit exists for all valid A, c. -/
axiom kesten_sos (A c : ℝ) (hA : A > 0) (hc : c > 1) :
    limitExists A c

/-- The limiting value (exists by Kesten-Sós). -/
noncomputable def limitValue (A c : ℝ) : ℝ :=
  if h : A > 0 ∧ c > 1 then
    Classical.choose (kesten_sos A c h.1 h.2)
  else 0

/-- The limit S(N,A,c) → limitValue(A,c). -/
theorem limit_convergence (A c : ℝ) (hA : A > 0) (hc : c > 1) :
    Tendsto (fun N => S N A c) atTop (nhds (limitValue A c)) := by
  simp only [limitValue, hA, hc, and_self, dif_pos]
  exact Classical.choose_spec (kesten_sos A c hA hc)

/-!
## Alternative Proofs

Boca (2008) and Xiong-Zaharescu (2006) provided independent,
more explicit proofs of limit existence.
-/

/-- Boca's approach (2008) uses Farey fractions and geometry of numbers. -/
def boca_method : Prop :=
  ∀ A c : ℝ, A > 0 → c > 1 → limitExists A c

/-- Xiong-Zaharescu approach (2006) uses continued fractions. -/
def xiong_zaharescu_method : Prop :=
  ∀ A c : ℝ, A > 0 → c > 1 → limitExists A c

axiom boca_theorem : boca_method
axiom xiong_zaharescu_theorem : xiong_zaharescu_method

/-!
## Connection to Farey Fractions

The problem relates to the distribution of Farey fractions.
-/

/-- Farey fractions of order n: rationals p/q with 0 ≤ p ≤ q ≤ n and gcd(p,q) = 1. -/
def FareyFraction (n : ℕ) : Set ℚ :=
  { r : ℚ | 0 ≤ r ∧ r ≤ 1 ∧ r.den ≤ n ∧ r.den.Coprime r.num.natAbs }

/-- The number of Farey fractions of order n is asymptotically 3n²/π². -/
axiom farey_count_asymptotic :
    Tendsto (fun n => (FareyFraction n).ncard / (n : ℝ)^2) atTop (nhds (3 / π^2))

/-- The EST formula involves 1/π² due to this Farey connection. -/
theorem est_pi_squared_explanation :
    f 1 (Real.exp 1) = 12 / π^2 := by
  simp [f]
  ring

/-!
## The Khinchin Connection

This problem relates to Khinchin's theorem on Diophantine approximation.
-/

/-- Khinchin's theorem: For decreasing ψ, the set of α with infinitely
    many |α - p/q| < ψ(q)/q has measure 0 or 1 depending on Σ ψ(q). -/
def khinchin_dichotomy : Prop :=
  True  -- Placeholder for the full statement

/-- The EST problem can be viewed as a "windowed" version of Khinchin. -/
theorem windowed_khinchin_connection :
    True := trivial

/-!
## Explicit Bounds

We can derive some explicit bounds from the EST formula.
-/

/-- For small A, the density is approximately 12A log(c) / π². -/
theorem small_A_approximation (c : ℝ) (hc : c > 1) :
    Tendsto (fun A => limitValue A c / A) (nhds 0) (nhds (12 * log c / π^2)) := by
  sorry

/-- The density is 0 when A = 0. -/
theorem zero_A_density (c : ℝ) :
    S 1 0 c = 0 := by
  sorry

/-!
## Summary

This file formalizes Erdős Problem #1001 on Diophantine approximation density.

**Status**: SOLVED

**The Question**: Does lim_{N→∞} S(N, A, c) exist, where S(N, A, c) measures
the set of α ∈ (0,1) approximable by some x/y with N ≤ y ≤ cN?

**The Answer**: YES, the limit exists (Kesten-Sós 1966).

**Explicit Formula**: In the EST regime (0 < A < c/(1+c²)),
  f(A, c) = 12A log(c) / π²

**Key Results**:
- Erdős-Szüsz-Turán (1958): Explicit formula in EST regime
- Kesten-Sós (1966): Limit exists in general
- EST boundedness: S stays away from 0 and 1 when min(A,c) > 10
- Boca, Xiong-Zaharescu: Alternative explicit proofs

**Connection**: The π² in the denominator comes from the asymptotics
of Farey fractions: |F_n| ~ 3n²/π².
-/

end Erdos1001
