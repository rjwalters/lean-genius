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

/-
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

/-
## Basic Properties

The measure S(N, A, c) satisfies natural bounds and monotonicity.
-/

/-
## The Limit Function

The main result is that S(N, A, c) converges as N → ∞.
-/

/-- The EST formula f(A, c) = 12A log(c)/π², valid in the EST regime. -/
noncomputable def f (A c : ℝ) : ℝ :=
  12 * A * log c / π^2

/-- f(A,c) is positive when A > 0 and c > 1: the approximation set has
    positive limiting measure, reflecting the density of rationals. -/
theorem f_pos (A c : ℝ) (hA : A > 0) (hc : c > 1) : f A c > 0 := by
  unfold f
  apply div_pos
  · apply mul_pos
    apply mul_pos
    · linarith
    · exact hA
    · exact Real.log_pos hc
  · positivity

/-- f is linear in A (for fixed c). -/
theorem f_linear_A (c A₁ A₂ : ℝ) :
    f (A₁ + A₂) c = f A₁ c + f A₂ c := by
  unfold f; ring

/-- f is zero when A = 0. -/
theorem f_zero_A (c : ℝ) : f 0 c = 0 := by
  unfold f; ring

/-- f is zero when c = 1 (since log 1 = 0). -/
theorem f_one_c (A : ℝ) : f A 1 = 0 := by
  unfold f
  simp [Real.log_one]

/-- The main question: Does lim S(N, A, c) exist? -/
def limitExists (A c : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (fun N => S N A c) atTop (nhds L)

/-
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

/-
## Boundedness Away from 0 and 1

EST also proved that when min(A,c) > 10, S stays bounded away from extremes.
-/

/-
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

/-
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

/-
## Connection to Farey Fractions

The problem relates to the distribution of Farey fractions.
-/

/-- Farey fractions of order n: rationals p/q with 0 ≤ p ≤ q ≤ n and gcd(p,q) = 1. -/
def FareyFraction (n : ℕ) : Set ℚ :=
  { r : ℚ | 0 ≤ r ∧ r ≤ 1 ∧ r.den ≤ n ∧ r.den.Coprime r.num.natAbs }

theorem est_pi_squared_explanation :
    f 1 (Real.exp 1) = 12 / π^2 := by
  simp [f]
  ring

/-
## Outside the EST Regime (Open Question oq-01)

The EST formula f(A,c) = 12A log(c)/π² holds when 0 < A < c/(1+c²).
Outside this regime (A ≥ c/(1+c²)), the limit still exists (Kesten-Sós)
but the explicit formula changes because the Farey approximation
intervals begin to overlap.

Key observations:
- In the EST regime, intervals |α - x/y| < A/y² for consecutive Farey
  fractions x/y are disjoint, so the total measure is a simple sum
- Outside EST, overlaps create inclusion-exclusion corrections
- The general formula involves the pair-correlation statistics of
  Farey fractions, studied by Boca-Cobeli-Zaharescu (2001)
- As A → ∞, limitValue(A,c) → 1 (full measure)

The explicit formula outside EST remains an active research direction.
-/

/-- The EST regime boundary value: A = c/(1+c²). -/
noncomputable def estBoundary (c : ℝ) : ℝ := c / (1 + c^2)

/-- The EST boundary is positive when c > 0. -/
theorem estBoundary_pos (c : ℝ) (hc : c > 0) : estBoundary c > 0 := by
  unfold estBoundary
  apply div_pos hc
  nlinarith [sq_nonneg c]

/-- Outside the EST regime: A ≥ c/(1+c²). Here the EST formula may
    undercount due to overlap, so limitValue(A,c) ≥ f(A,c). -/
def outsideESTRegime (A c : ℝ) : Prop :=
  0 < A ∧ c / (1 + c^2) ≤ A

/-- In the EST regime, the limit equals f(A,c). Outside, by Kesten-Sós,
    the limit still exists but may differ from f(A,c). -/
theorem limit_in_est_regime (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    limitValue A c = f A c := by
  have hconv := erdos_szusz_turan A c hA hc hregime
  have hconv2 := limit_convergence A c hA hc
  exact tendsto_nhds_unique hconv2 hconv

/-
## Summary

**Status**: SOLVED

**The Question**: Does lim_{N→∞} S(N, A, c) exist, where S(N, A, c) measures
the set of α ∈ (0,1) approximable by some x/y with N ≤ y ≤ cN?

**The Answer**: YES, the limit exists (Kesten-Sós 1966).

**Explicit Formula**: In the EST regime (0 < A < c/(1+c²)),
  f(A, c) = 12A log(c) / π²

**Key Results**:
- Erdős-Szüsz-Turán (1958): Explicit formula in EST regime
- Kesten-Sós (1966): Limit exists in general
- Boca, Xiong-Zaharescu: Alternative explicit proofs
- f(A,c) > 0 for A > 0, c > 1 (proved)
- limitValue = f in EST regime (proved via uniqueness of limits)

**Open**: Explicit formula outside EST regime (A ≥ c/(1+c²)).
-/

/-- **Erdős Problem #1001: SOLVED**
    The limit lim S(N,A,c) exists for all valid A, c. -/
theorem erdos_1001 (A c : ℝ) (hA : A > 0) (hc : c > 1) :
    limitExists A c :=
  kesten_sos A c hA hc

end Erdos1001
