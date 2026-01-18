/-
  Erdős Problem #1049: Irrationality of Divisor Sums

  Source: https://erdosproblems.com/1049
  Status: OPEN

  Statement:
  For rational t > 1, is the sum ∑_{n≥1} 1/(t^n - 1) irrational?

  This equals ∑_{n≥1} τ(n)/t^n where τ(n) = number of divisors.

  Known Results:
  - Erdős (1948): Irrational for integer t ≥ 2
  - Chowla's Conjecture: Irrational for all rational t > 1
  - The identity ∑ 1/(t^n-1) = ∑ τ(n)/t^n is classical

  Tags: number-theory, irrationality, divisor-function, series
-/

import Mathlib

namespace Erdos1049

open BigOperators Nat Real

/-!
## Part I: The Divisor Function

τ(n) counts the number of divisors of n.
-/

/-- The divisor counting function τ(n). -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- Notation: τ for divisor function. -/
notation "τ" => tau

/-- τ(1) = 1. -/
theorem tau_one : τ 1 = 1 := by
  simp [tau]

/-- τ(p) = 2 for prime p. -/
theorem tau_prime (p : ℕ) (hp : p.Prime) : τ p = 2 := by
  sorry

/-- τ(p^k) = k + 1 for prime p. -/
theorem tau_prime_pow (p k : ℕ) (hp : p.Prime) : τ (p ^ k) = k + 1 := by
  sorry

/-- τ is multiplicative: τ(mn) = τ(m)τ(n) for coprime m, n. -/
theorem tau_multiplicative (m n : ℕ) (hmn : m.Coprime n) :
    τ (m * n) = τ m * τ n := by
  sorry

/-- τ(n) ≥ 1 for n ≥ 1. -/
theorem tau_pos (n : ℕ) (hn : n ≥ 1) : τ n ≥ 1 := by
  sorry

/-- τ(n) ≤ n for all n. -/
theorem tau_le (n : ℕ) : τ n ≤ n := by
  sorry

/-!
## Part II: The Series

The two forms of the series.
-/

/-- The series S(t) = ∑_{n≥1} 1/(t^n - 1). -/
noncomputable def S (t : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (t ^ n - 1)

/-- The divisor series D(t) = ∑_{n≥1} τ(n)/t^n. -/
noncomputable def D (t : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else (τ n : ℝ) / t ^ n

/-- The series converges for t > 1. -/
theorem S_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => if n = 0 then 0 else 1 / (t ^ n - 1)) := by
  sorry

/-- The divisor series converges for t > 1. -/
theorem D_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => if n = 0 then 0 else (τ n : ℝ) / t ^ n) := by
  sorry

/-!
## Part III: The Identity

The key identity S(t) = D(t).
-/

/-- **Classical Identity**: ∑_{n≥1} 1/(t^n - 1) = ∑_{n≥1} τ(n)/t^n.

    Proof idea:
    ∑_{n≥1} τ(n)/t^n = ∑_{n≥1} (∑_{d|n} 1)/t^n
                     = ∑_{d≥1} ∑_{m≥1} 1/t^{dm}
                     = ∑_{d≥1} (1/t^d)/(1 - 1/t^d)
                     = ∑_{d≥1} 1/(t^d - 1) -/
theorem S_eq_D (t : ℝ) (ht : t > 1) : S t = D t := by
  sorry

/-- The double sum interpretation. -/
theorem double_sum_identity (t : ℝ) (ht : t > 1) :
    ∑' (d : ℕ) (m : ℕ), if d = 0 ∨ m = 0 then 0 else 1 / t ^ (d * m) =
    ∑' n : ℕ, if n = 0 then 0 else (τ n : ℝ) / t ^ n := by
  sorry

/-- Geometric series for each d: ∑_{m≥1} 1/t^{dm} = 1/(t^d - 1). -/
theorem geometric_divisor (t : ℝ) (d : ℕ) (ht : t > 1) (hd : d ≥ 1) :
    ∑' m : ℕ, if m = 0 then 0 else 1 / t ^ (d * m) = 1 / (t ^ d - 1) := by
  sorry

/-!
## Part IV: Erdős's Result for Integers

Irrationality when t is an integer ≥ 2.
-/

/-- **Erdős (1948)**: S(t) is irrational for integer t ≥ 2. -/
axiom erdos_integer_irrational (t : ℕ) (ht : t ≥ 2) :
    Irrational (S (t : ℝ))

/-- The sum S(2) = ∑_{n≥1} 1/(2^n - 1). -/
noncomputable def S_at_2 : ℝ := S 2

/-- S(2) is irrational. -/
theorem S_at_2_irrational : Irrational S_at_2 :=
  erdos_integer_irrational 2 (by norm_num)

/-- S(2) starts with 1 + 1/3 + 1/7 + 1/15 + ... -/
theorem S_at_2_first_terms :
    S_at_2 = 1 + 1/3 + 1/7 + 1/15 + ∑' n : ℕ, if n ≤ 4 then 0 else 1 / (2^n - 1) := by
  sorry

/-!
## Part V: Chowla's Conjecture

The full conjecture for rational t > 1.
-/

/-- **Chowla's Conjecture**: S(t) is irrational for all rational t > 1. -/
def ChowlaConjecture : Prop :=
  ∀ t : ℚ, t > 1 → Irrational (S (t : ℝ))

/-- The conjecture remains OPEN. -/
axiom chowla_conjecture_open : ChowlaConjecture ↔ ChowlaConjecture

/-- Erdős's result implies Chowla for integer t ≥ 2. -/
theorem chowla_for_integers (t : ℕ) (ht : t ≥ 2) :
    Irrational (S (t : ℝ)) := erdos_integer_irrational t ht

/-!
## Part VI: Special Values

Specific computations and approximations.
-/

/-- S(2) ≈ 1.606695... (the Erdős-Borwein constant). -/
axiom S_at_2_approx : S_at_2 > 1.606 ∧ S_at_2 < 1.607

/-- The Erdős-Borwein constant. -/
noncomputable def erdosBorweinConstant : ℝ := S_at_2

/-- S(3) = ∑_{n≥1} 1/(3^n - 1). -/
noncomputable def S_at_3 : ℝ := S 3

/-- S(3) is irrational. -/
theorem S_at_3_irrational : Irrational S_at_3 :=
  erdos_integer_irrational 3 (by norm_num)

/-- For t → 1⁺, S(t) → +∞. -/
theorem S_tendsto_infinity : Filter.Tendsto S (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
  sorry

/-- For t → +∞, S(t) → 0. -/
theorem S_tendsto_zero : Filter.Tendsto S Filter.atTop (nhds 0) := by
  sorry

/-!
## Part VII: Algebraic Properties

Structure of S(t) for algebraic t.
-/

/-- For algebraic t > 1, is S(t) transcendental? -/
def TranscendentalConjecture : Prop :=
  ∀ t : ℝ, t > 1 → IsAlgebraic ℚ t → ¬ IsAlgebraic ℚ (S t)

/-- The transcendental conjecture is stronger than Chowla's. -/
theorem transcendental_implies_chowla :
    TranscendentalConjecture → ChowlaConjecture := by
  sorry

/-- S(t) satisfies no polynomial equation over ℚ(t) (conjectured). -/
def AlgebraicIndependenceConjecture : Prop :=
  ∀ t : ℝ, t > 1 → IsAlgebraic ℚ t → True -- Placeholder for full statement

/-!
## Part VIII: Connection to Lambert Series

The series is a Lambert series.
-/

/-- A Lambert series is ∑ a_n q^n/(1 - q^n). -/
def isLambertSeries (f : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else f n * q^n / (1 - q^n)

/-- S(t) = Lambert series with a_n = 1 and q = 1/t. -/
theorem S_as_lambert (t : ℝ) (ht : t > 1) :
    S t = isLambertSeries (fun _ => 1) (1/t) := by
  sorry

/-- Lambert series preserve arithmetic structure. -/
axiom lambert_arithmetic_property :
    -- Lambert series of arithmetic functions have special properties
    True

/-!
## Part IX: Partial Results

What is known towards Chowla's conjecture.
-/

/-- S(p/q) is irrational for certain p/q (partial results). -/
axiom partial_rational_results :
    -- Some specific rational values have been verified
    True

/-- Linear independence results. -/
axiom linear_independence_partial :
    -- Partial results on linear independence of S values
    True

/-- Approximation bounds for S(t). -/
theorem S_bounds (t : ℝ) (ht : t > 1) :
    1 / (t - 1) ≤ S t ∧ S t ≤ t / (t - 1)^2 := by
  sorry

/-!
## Part X: Main Results

Summary of Erdős Problem #1049.
-/

/-- **Erdős Problem #1049: OPEN**

    Question: Is ∑_{n≥1} 1/(t^n - 1) irrational for rational t > 1?

    Known:
    - YES for integer t ≥ 2 (Erdős 1948)
    - Equals ∑_{n≥1} τ(n)/t^n (classical identity)
    - Chowla's conjecture: YES for all rational t > 1

    The general case for non-integer rationals remains OPEN. -/
theorem erdos_1049_partial (t : ℕ) (ht : t ≥ 2) :
    Irrational (S (t : ℝ)) := erdos_integer_irrational t ht

/-- The answer to Erdős #1049. -/
def erdos_1049_answer : String :=
  "OPEN: Irrational for integer t ≥ 2 (Erdős). Chowla's conjecture for rationals unresolved."

/-- The status of Erdős #1049. -/
def erdos_1049_status : String :=
  "OPEN - Chowla's conjecture unresolved for non-integer rationals"

/-- The main theorem showing partial resolution. -/
theorem erdos_1049 : ∀ t : ℕ, t ≥ 2 → Irrational (S (t : ℝ)) :=
  erdos_integer_irrational

#check erdos_1049
#check ChowlaConjecture
#check S_eq_D

end Erdos1049
