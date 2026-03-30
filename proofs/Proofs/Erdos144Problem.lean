/-
Erdős Problem #144: Propinquity of Divisors

Source: https://erdosproblems.com/144
Status: SOLVED (Maier-Tenenbaum 1984)
Prize: $250 (Tenenbaum reported receiving $650)

Statement:
The density of integers which have two divisors d₁, d₂ such that
d₁ < d₂ < 2d₁ exists and equals 1.

Stronger Version:
For any constant c > 1, the density of integers with divisors
d₁ < d₂ < c·d₁ also equals 1.

Resolution:
Maier and Tenenbaum proved YES to both versions in 1984.
The threshold β = log 3 - 1 separates density 1 from density 0
for the refined version with d₂ < d₁(1 + (log n)^{-β}).

Historical Note:
Erdős initially claimed a proof in 1964 but retracted it in 1979.
Erdős and Hall proved the complementary result (density 0 for β > log 3 - 1).

References:
- Maier-Tenenbaum [MaTe84]: Complete proof of density 1
- Erdős-Hall [ErHa79]: Density 0 for β > log 3 - 1
- Erdős [Er79]: Posed stronger version with c > 1
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

namespace Erdos144

/- ## Part I: Basic Definitions -/

/-- **Natural density of a set:**
    d(A) = lim_{n→∞} |A ∩ {1,...,n}| / n. -/
def naturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N,
    |((Finset.filter (· ∈ A) (Finset.range n)).card : ℝ) / n - d| < ε

/-- **Close divisors property:**
    An integer n has "close divisors" if there exist divisors d₁ < d₂
    with d₂ < 2d₁. -/
def hasCloseDivisors (n : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁

/-- **c-close divisors property:**
    For constant c > 1, n has c-close divisors if there exist
    divisors d₁ < d₂ with d₂ < c·d₁. -/
def hasCloseDivisorsC (c : ℝ) (n : ℕ) : Prop :=
  c > 1 ∧ ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ (d₂ : ℝ) < c * d₁

/-- The set of integers with close divisors. -/
def closeDivisorsSet : Set ℕ := {n | hasCloseDivisors n}

/-- The set with c-close divisors. -/
def closeDivisorsSetC (c : ℝ) : Set ℕ := {n | hasCloseDivisorsC c n}

/- ## Part II: The Main Theorem -/

/-- **Erdős Problem #144 (Basic Version):**
    The density of integers with close divisors equals 1. -/
def erdos_144_conjecture : Prop :=
  naturalDensity closeDivisorsSet 1

/-- **Erdős Problem #144 (Strong Version):**
    For any c > 1, the density of integers with c-close divisors equals 1. -/
def erdos_144_strong_conjecture (c : ℝ) : Prop :=
  c > 1 → naturalDensity (closeDivisorsSetC c) 1

/-- **Maier-Tenenbaum Theorem (1984):**
    The conjecture is true: density equals 1.
    Proved using divisor distribution theory and probabilistic number theory. -/
axiom maier_tenenbaum_theorem : erdos_144_conjecture

/-- **Maier-Tenenbaum Strong Theorem:**
    For any c > 1, the density of c-close divisors equals 1. -/
axiom maier_tenenbaum_strong : ∀ c : ℝ, erdos_144_strong_conjecture c

/- ## Part III: The Threshold β = log 3 - 1 -/

/-- **The critical exponent:**
    β* = log 3 - 1 ≈ 0.0986 is the threshold for the refined version. -/
def criticalExponent : ℝ := Real.log 3 - 1

/-- **Refined close divisors with log factor:**
    n has (β)-close divisors if there exist d₁ < d₂ with
    d₂ < d₁(1 + (log n)^{-β}). -/
def hasRefinedCloseDivisors (β : ℝ) (n : ℕ) : Prop :=
  n ≥ 2 ∧ ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧
    (d₂ : ℝ) < d₁ * (1 + (Real.log n) ^ (-β))

/-- The set with (β)-close divisors. -/
def refinedCloseDivisorsSet (β : ℝ) : Set ℕ :=
  {n | hasRefinedCloseDivisors β n}

/-- **Erdős-Hall Theorem (1979):**
    If β > log 3 - 1, the density of (β)-close divisors equals 0.
    This complementary result was proved after Erdős retracted his 1964 claim. -/
axiom erdos_hall_theorem (β : ℝ) :
    β > criticalExponent →
    naturalDensity (refinedCloseDivisorsSet β) 0

/-- **Maier-Tenenbaum Refined Theorem:**
    If β < log 3 - 1, the density of (β)-close divisors equals 1.
    This completed the picture, vindicating Erdős's original conjecture. -/
axiom maier_tenenbaum_refined (β : ℝ) :
    β < criticalExponent →
    naturalDensity (refinedCloseDivisorsSet β) 1

/-- **Phase transition at β* = log 3 - 1:**
    The density jumps from 0 to 1 at the critical exponent. -/
theorem phase_transition :
    (∀ β > criticalExponent, naturalDensity (refinedCloseDivisorsSet β) 0) ∧
    (∀ β < criticalExponent, naturalDensity (refinedCloseDivisorsSet β) 1) :=
  ⟨erdos_hall_theorem, maier_tenenbaum_refined⟩

/- ## Part IV: Examples -/

/-- Every divisor of a prime power is a power of that prime. -/
private lemma dvd_prime_pow_eq_pow {p : ℕ} (hp : Nat.Prime p) {k d : ℕ}
    (hd : d ∣ p ^ k) : ∃ j ≤ k, d = p ^ j := by
  induction k with
  | zero => exact ⟨0, le_refl 0, Nat.eq_one_of_dvd_one (by rwa [pow_zero] at hd)⟩
  | succ n ih =>
    by_cases h : p ∣ d
    · obtain ⟨d', rfl⟩ := h
      obtain ⟨j, hj, rfl⟩ := ih (by
        have : p ^ (n + 1) = p * p ^ n := by ring
        rw [this] at hd
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos hd)
      exact ⟨j + 1, by omega, by ring⟩
    · obtain ⟨j, hj, rfl⟩ := ih (by
        have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr h).symm
        rw [pow_succ] at hd
        exact hcop.dvd_of_dvd_mul_right hd)
      exact ⟨j, by omega, rfl⟩

/-- **Prime powers have no close divisors:**
    If n = p^k (prime power), any two divisors d₁ = p^a < d₂ = p^b satisfy
    d₂ ≥ p · d₁ ≥ 2d₁ (strict: d₂ < 2d₁ is impossible since p ≥ 2). -/
theorem prime_powers_fail : ∀ p k : ℕ, Nat.Prime p → k ≥ 1 →
    ¬hasCloseDivisors (p ^ k) := by
  intro p k hp _
  intro ⟨d₁, d₂, hd1, hd2, hlt, hlt2⟩
  obtain ⟨a, _, rfl⟩ := dvd_prime_pow_eq_pow hp hd1
  obtain ⟨b, _, rfl⟩ := dvd_prime_pow_eq_pow hp hd2
  -- p^a < p^b with a < b (strict monotonicity of p^· for p ≥ 2)
  have hab : a < b := by
    by_contra h; push_neg at h
    exact not_lt.mpr (Nat.pow_le_pow_right hp.pos h) hlt
  -- p^b ≥ 2 · p^a, contradicting p^b < 2 · p^a
  have : 2 * p ^ a ≤ p ^ b :=
    calc 2 * p ^ a ≤ p * p ^ a := Nat.mul_le_mul_right _ hp.two_le
      _ = p ^ (a + 1) := by ring
      _ ≤ p ^ b := Nat.pow_le_pow_right hp.pos (by omega)
  omega

/-- **Example: 6 has close divisors.**
    6 = 2 · 3, divisors are 1, 2, 3, 6.
    We have 2 < 3 < 2 · 2 = 4. So d₁ = 2, d₂ = 3 works. -/
example : hasCloseDivisors 6 := by
  use 2, 3
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-- **Example: 12 has close divisors.**
    12 = 2² · 3, divisors are 1, 2, 3, 4, 6, 12.
    We have 3 < 4 < 6 = 2 · 3. So d₁ = 3, d₂ = 4 works. -/
example : hasCloseDivisors 12 := by
  use 3, 4
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/- ## Part V: Summary -/

/-- **Summary of Erdős Problem #144:**

PROBLEM: Does the density of integers with close divisors
(d₁ < d₂ < 2d₁) exist and equal 1?

STATUS: SOLVED (YES) by Maier-Tenenbaum 1984

KEY RESULTS:
1. Density equals 1 for any c > 1 (not just c = 2)
2. Threshold β* = log 3 - 1 for refined version
3. β < β* ⟹ density 1 (Maier-Tenenbaum)
4. β > β* ⟹ density 0 (Erdős-Hall)

The result demonstrates that "generic" integers have divisors that
cluster together, a manifestation of probabilistic number theory.
The phase transition at β* = log 3 - 1 ≈ 0.0986 gives a precise
characterization. -/
theorem erdos_144_summary :
    erdos_144_conjecture ∧
    (∀ c > 1, erdos_144_strong_conjecture c) ∧
    (∀ β > criticalExponent, naturalDensity (refinedCloseDivisorsSet β) 0) ∧
    (∀ β < criticalExponent, naturalDensity (refinedCloseDivisorsSet β) 1) :=
  ⟨maier_tenenbaum_theorem,
   fun c hc => maier_tenenbaum_strong c,
   erdos_hall_theorem,
   maier_tenenbaum_refined⟩

end Erdos144
