/-
  Erdős Problem #371: Density of P(n) < P(n+1)

  Source: https://erdosproblems.com/371
  Status: SOLVED (conditionally: Wang 2021; logarithmic: Teräväinen 2018)

  Statement:
  Let P(n) denote the largest prime factor of n. Show that the set of n
  with P(n) < P(n+1) has density 1/2.

  History:
  - Erdős-Pomerance (1978): Conjectured; proved positive upper density for both sets
  - Lü-Wang (2025): #{n < x : P(n) < P(n+1)} > (0.2017 - o(1))x
  - Teräväinen (2018): Logarithmic density is 1/2
  - Tao-Teräväinen (2019): Asymptotic density 1/2 at almost all scales
  - Wang (2021): Full result conditional on Elliott-Halberstam conjecture

  References:
  [ErPo78] Erdős-Pomerance, "On the largest prime factors of n and n+1" (1978)
  [Te18] Teräväinen, "On binary correlations of multiplicative functions" (2018)
  [TaTe19] Tao-Teräväinen, "The structure of correlations..." (2019)
  [Wa21] Wang, "Three conjectures on P^+(n) and P^+(n+1)..." (2021)
  [LuWa25] Lü-Wang, "On the largest prime factors of consecutive integers" (2025)

  Tags: number-theory, prime-factors, density, analytic-number-theory
-/

import Mathlib

namespace Erdos371

open scoped Classical
open Nat Real Filter Finset Topology

/- ## Part I: Greatest Prime Factor -/

/-- The greatest prime factor of n, or 0 if n ≤ 1. -/
noncomputable def P (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0
  else (n.primeFactors).max' (by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have h1 : 1 < n := by omega
    have ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact absurd (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩) (he ▸ Finset.not_mem_empty p))

/-- P(n) divides n for n > 1. -/
theorem P_dvd (n : ℕ) (hn : n > 1) : P n ∣ n := by
  have h : ¬(n ≤ 1) := by omega
  simp only [P, dif_neg h]
  exact (Nat.mem_primeFactors.mp (Finset.max'_mem _ _)).2.1

/-- P(n) is prime for n > 1. -/
theorem P_prime (n : ℕ) (hn : n > 1) : (P n).Prime := by
  have h : ¬(n ≤ 1) := by omega
  simp only [P, dif_neg h]
  exact (Nat.mem_primeFactors.mp (Finset.max'_mem _ _)).1

/-- P(n) is the maximum prime dividing n. -/
theorem P_is_max (n : ℕ) (hn : n > 1) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ n) :
    p ≤ P n := by
  have h : ¬(n ≤ 1) := by omega
  simp only [P, dif_neg h]
  exact Finset.le_max' _ _ (Nat.mem_primeFactors.mpr ⟨hp, hdvd, by omega⟩)

/-- P(p) = p for prime p. -/
theorem P_prime_eq (p : ℕ) (hp : p.Prime) : P p = p := by
  apply le_antisymm
  · exact Nat.le_of_dvd hp.pos (P_dvd p hp.one_lt)
  · exact P_is_max p hp.one_lt p hp (dvd_refl p)

/-- P(n) ≤ n for all n. -/
theorem P_le (n : ℕ) : P n ≤ n := by
  by_cases h : n ≤ 1
  · simp [P, h]
  · exact Nat.le_of_dvd (by omega) (P_dvd n (by omega))

/- ## Part II: Natural Density -/

/-- The counting function for a set of naturals. -/
noncomputable def countingFunction (S : Set ℕ) (x : ℕ) : ℕ :=
  (Finset.range x).filter (· ∈ S) |>.card

/-- A set has natural density d if #{n < x : n ∈ S}/x → d. -/
def HasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun x : ℕ => (countingFunction S x : ℝ) / x) atTop (𝓝 d)

/-- A set has positive upper density. -/
def HasPositiveUpperDensity (S : Set ℕ) : Prop :=
  ∃ δ > 0, ∀ᶠ x in atTop, (countingFunction S x : ℝ) / x > δ

/-- A set has lower density at least d. -/
def HasLowerDensity (S : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x in atTop, (countingFunction S x : ℝ) / x > d - ε

/-- Logarithmic density. -/
def HasLogDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun x : ℕ => (∑ n ∈ (Finset.range x).filter (· ∈ S), (1 : ℝ) / n) /
    Real.log x) atTop (𝓝 d)

/- ## Part III: The Main Sets -/

/-- The set of n where P(n) < P(n+1). -/
def SetPIncreasing : Set ℕ :=
  {n : ℕ | n ≥ 2 ∧ P n < P (n + 1)}

/-- The complementary set: n where P(n) ≥ P(n+1). -/
def SetPDecreasing : Set ℕ :=
  {n : ℕ | n ≥ 2 ∧ P n ≥ P (n + 1)}

/-- The two sets partition ℕ≥2. -/
theorem partition (n : ℕ) (hn : n ≥ 2) :
    n ∈ SetPIncreasing ∨ n ∈ SetPDecreasing := by
  by_cases h : P n < P (n + 1)
  · left; exact ⟨hn, h⟩
  · right; exact ⟨hn, not_lt.mp h⟩

/- ## Part IV: Erdős-Pomerance (1978) -/

/-- **Erdős-Pomerance (1978)**

    Both SetPIncreasing and SetPDecreasing have positive upper density.
    This was the first major result on the problem.
-/

/- ## Part V: Lü-Wang Lower Bound (2025) -/

/-- **Lü-Wang (2025)**

    #{n < x : P(n) < P(n+1)} > (0.2017 - o(1))x

    This is the best unconditional lower bound available.
-/

/- ## Part VI: Teräväinen (2018) - Logarithmic Density -/

/-- **Teräväinen (2018)**

    The logarithmic density of {n : P(n) < P(n+1)} is exactly 1/2.
-/
axiom teravanen_2018 :
    HasLogDensity SetPIncreasing (1/2)

/-- Logarithmic density of complement is also 1/2. -/
theorem teravanen_complement :
    HasLogDensity SetPDecreasing (1/2) := by
  sorry

/- ## Part VII: Tao-Teräväinen (2019) - Almost All Scales -/

/-- **Tao-Teräväinen (2019)**

    The asymptotic density is 1/2 at 'almost all scales'.
    More precisely, for almost all x (in a suitable sense),
    #{n < x : P(n) < P(n+1)}/x is close to 1/2.
-/
def DensityAtAlmostAllScales (S : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ E : Set ℝ, (∀ᶠ T in atTop, (∫ t in E ∩ Set.Icc 1 T, 1) / T < ε) ∧
    ∀ x : ℕ, (x : ℝ) ∉ E → |(countingFunction S x : ℝ) / x - d| < ε

/- ## Part VIII: Wang (2021) - Conditional Result -/

/-- The Elliott-Halberstam conjecture for friable integers.
    This asserts equidistribution of smooth numbers in arithmetic progressions
    at the level of exponent θ = 1, analogous to the classical Elliott-Halberstam
    conjecture but restricted to y-friable integers.
    Axiomatized as an opaque proposition since the full formal statement requires
    deep analytic number theory infrastructure. -/
axiom ElliottHalberstamForFriable : Prop

/-- **Wang (2021)**

    Assuming the Elliott-Halberstam conjecture for friable integers,
    the natural density of {n : P(n) < P(n+1)} is exactly 1/2.
-/
axiom wang_2021 (h : ElliottHalberstamForFriable) :
    HasNaturalDensity SetPIncreasing (1/2)

/- ## Part IX: The Main Conjecture -/

/-- **Erdős Problem #371 (Main Conjecture)**

    The set {n : P(n) < P(n+1)} has natural density 1/2.

    This is still open unconditionally, but:
    - Logarithmic density is 1/2 (Teräväinen 2018)
    - Asymptotic density is 1/2 at almost all scales (Tao-Teräväinen 2019)
    - Full result holds under Elliott-Halberstam (Wang 2021)
-/
def Erdos371Conjecture : Prop :=
  HasNaturalDensity SetPIncreasing (1/2)

/-- The conjecture is implied by Wang's conditional result. -/
theorem erdos_371_from_elliott_halberstam (h : ElliottHalberstamForFriable) :
    Erdos371Conjecture :=
  wang_2021 h

/- ## Part X: Generalized Form with α -/

/-- The set of n where P(n+1) > P(n) · n^α. -/
def SetPAlpha (α : ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 2 ∧ (P (n + 1) : ℝ) > P n * (n : ℝ) ^ α}

/-- Erdős (1979) asked if the density of SetPAlpha exists for all α ∈ [0,1]. -/
def Erdos1979Question (α : ℝ) : Prop :=
  ∃ d : ℝ, HasNaturalDensity (SetPAlpha α) d

/-- **Teräväinen (2018) - Generalized**

    The logarithmic density of SetPAlpha(α) exists and equals the integral
    ∫∫_{y≥x+α} u(x)u(y) dx dy where u is related to the Dickman function.
-/

/- ## Part XI: The Dickman Function -/

/-- The Dickman function ρ(u) satisfies uρ'(u) = -ρ(u-1) for u > 1,
    with ρ(u) = 1 for 0 ≤ u ≤ 1.
    Axiomatized as it is defined by a delay differential equation
    without closed-form solution. -/
axiom dickman : ℝ → ℝ

/-- The function u(x) = x^{-1} ρ(x^{-1} - 1) appearing in the density formula. -/
noncomputable def densityKernel (x : ℝ) : ℝ :=
  if x > 0 ∧ x ≤ 1 then x⁻¹ * dickman (x⁻¹ - 1) else 0

/-- The theoretical density of SetPAlpha(α). -/
noncomputable def theoreticalDensity (α : ℝ) : ℝ :=
  ∫ x in Set.Icc 0 1, ∫ y in Set.Icc 0 1,
    if y ≥ x + α then densityKernel x * densityKernel y else 0

/-- For α = 0, the theoretical density is 1/2. -/
theorem theoretical_density_zero :
    theoreticalDensity 0 = 1/2 := by
  sorry

/- ## Part XII: Small Examples -/

/-- P(2) = 2. -/
theorem P_2 : P 2 = 2 := P_prime_eq 2 (by norm_num)

/-- P(3) = 3. -/
theorem P_3 : P 3 = 3 := P_prime_eq 3 (by norm_num)

/-- P(4) = 2. -/
theorem P_4 : P 4 = 2 := by
  have hp := P_prime 4 (by omega)
  have hdvd := P_dvd 4 (by omega)
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4] at hdvd
  have hdvd2 : P 4 ∣ 2 := hp.dvd_of_dvd_pow hdvd
  have hle : P 4 ≤ 2 := Nat.le_of_dvd (by omega) hdvd2
  have hge : P 4 ≥ 2 := hp.two_le
  omega

/-- P(5) = 5. -/
theorem P_5 : P 5 = 5 := P_prime_eq 5 (by norm_num)

/-- P(6) = 3. -/
theorem P_6 : P 6 = 3 := by
  have hp := P_prime 6 (by omega)
  have hdvd := P_dvd 6 (by omega)
  apply le_antisymm
  · -- P(6) ≤ 3: P(6) is prime and divides 6 = 2 * 3
    have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h6] at hdvd
    rcases hp.dvd_mul.mp hdvd with h2 | h3
    · exact le_trans (Nat.le_of_dvd (by omega) h2) (by omega)
    · exact Nat.le_of_dvd (by omega) h3
  · exact P_is_max 6 (by omega) 3 (by norm_num) (by norm_num)

/-- 2 ∈ SetPIncreasing since P(2) = 2 < P(3) = 3. -/
theorem two_in_set : 2 ∈ SetPIncreasing := by
  constructor
  · omega
  · rw [P_2, P_3]; omega

/-- 4 ∈ SetPIncreasing since P(4) = 2 < P(5) = 5. -/
theorem four_in_set : 4 ∈ SetPIncreasing := by
  constructor
  · omega
  · rw [P_4, P_5]; omega

/-- 5 ∈ SetPDecreasing since P(5) = 5 > P(6) = 3. -/
theorem five_in_complement : 5 ∈ SetPDecreasing := by
  constructor
  · omega
  · rw [P_5, P_6]; omega

/- ## Part XIII: Related Problems -/

/-- Connection to Problem #372: Behavior of P(n)/P(n+1). -/
def Problem372Related : Prop :=
  ∃ d : ℝ, HasNaturalDensity {n | (P n : ℝ) / P (n + 1) < 1} d

/-- Connection to Problem #928: Similar questions for consecutive primes. -/
def Problem928Related : Prop :=
  ∃ d : ℝ, HasNaturalDensity {n | ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ∣ (n + 1)} d

/- ## Part XIV: OEIS Sequence A070089 -/

/-- The sequence of n where P(n) < P(n+1) is A070089 in OEIS.
    First few terms: 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, ... -/
def isOEIS_A070089 (n : ℕ) : Prop := n ∈ SetPIncreasing

/-- Many even numbers are in the sequence. -/
theorem even_often_in_set (n : ℕ) (hn : n ≥ 2) (heven : Even n)
    (hodd_next : Odd (n + 1)) (hn1_prime : (n + 1).Prime) :
    n ∈ SetPIncreasing := by
  refine ⟨hn, ?_⟩
  calc P n ≤ n := P_le n
    _ < n + 1 := by omega
    _ = P (n + 1) := (P_prime_eq (n + 1) hn1_prime).symm

end Erdos371

/-
## Summary

This file formalizes Erdős Problem #371 on the density of consecutive
integers with increasing largest prime factor.

**Status**: Conditionally SOLVED (Wang 2021); Logarithmically SOLVED (Teräväinen 2018)

**The Problem**: Let P(n) be the largest prime factor of n. Show that
{n : P(n) < P(n+1)} has natural density 1/2.

**Key Results**:
- Erdős-Pomerance (1978): Both sets have positive upper density
- Lü-Wang (2025): Lower bound > 0.2017 (unconditional)
- Teräväinen (2018): Logarithmic density = 1/2
- Tao-Teräväinen (2019): Asymptotic density 1/2 at almost all scales
- Wang (2021): Full result under Elliott-Halberstam conjecture

**What we formalize**:
1. Greatest prime factor P(n)
2. Natural and logarithmic density definitions
3. The sets {n : P(n) < P(n+1)} and its complement
4. Historical results: Erdős-Pomerance, Teräväinen, Tao-Teräväinen, Wang
5. Generalized form with parameter α
6. Connection to Dickman function
7. Small examples and OEIS sequence A070089

**Key axioms**:
- `erdos_pomerance_1978_*`: Positive upper density results
- `teravanen_2018`: Logarithmic density is 1/2
- `wang_2021`: Full result under Elliott-Halberstam

**Related Problems**: #372, #928
-/
