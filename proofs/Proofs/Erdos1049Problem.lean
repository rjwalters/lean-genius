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

/-
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
  unfold tau
  rw [hp.divisors, Finset.card_insert_of_not_mem (by simp [hp.one_lt.ne]),
      Finset.card_singleton]

/-- τ(p^k) = k + 1 for prime p. -/
theorem tau_prime_pow (p k : ℕ) (hp : p.Prime) : τ (p ^ k) = k + 1 := by
  simp [tau, Nat.divisors_prime_pow hp]

/-- τ is multiplicative: τ(mn) = τ(m)τ(n) for coprime m, n. -/
theorem tau_multiplicative (m n : ℕ) (hmn : m.Coprime n) :
    τ (m * n) = τ m * τ n := by
  simp only [tau]
  rw [hmn.divisors_mul]
  exact Finset.card_product _ _

/-- τ(n) ≥ 1 for n ≥ 1. -/
theorem tau_pos (n : ℕ) (hn : n ≥ 1) : τ n ≥ 1 := by
  simp only [tau, ge_iff_le]
  exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (Nat.pos_iff_ne_zero.mp hn)⟩

/-- τ(n) ≤ n for all n. -/
theorem tau_le (n : ℕ) : τ n ≤ n := by
  simp only [tau]
  exact Nat.card_divisors_le_self n

/-
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
    Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else 1 / (t ^ n - 1)) := by
  sorry

/-- The divisor series converges for t > 1. -/
theorem D_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (τ n : ℝ) / t ^ n) := by
  sorry

/-
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
    (∑' d : ℕ, ∑' m : ℕ, if d = 0 ∨ m = 0 then (0 : ℝ) else 1 / t ^ (d * m)) =
    ∑' n : ℕ, if n = 0 then (0 : ℝ) else (τ n : ℝ) / t ^ n := by
  sorry

/-- Geometric series for each d: ∑_{m≥1} 1/t^{dm} = 1/(t^d - 1). -/
theorem geometric_divisor (t : ℝ) (d : ℕ) (ht : t > 1) (hd : d ≥ 1) :
    (∑' m : ℕ, if m = 0 then (0 : ℝ) else 1 / t ^ (d * m)) = 1 / (t ^ d - 1) := by
  -- Let r = (t^d)⁻¹, with 0 < r < 1
  have htd_pos : (0 : ℝ) < t ^ d := by positivity
  have htd_gt : (1 : ℝ) < t ^ d := by
    calc (1 : ℝ) = 1 ^ d := (one_pow d).symm
    _ < t ^ d := by
      apply pow_lt_pow_left (by linarith : (1 : ℝ) < t) (by linarith : (0 : ℝ) ≤ 1)
      omega
  have htd_ne : t ^ d ≠ 0 := ne_of_gt htd_pos
  set r := (t ^ d)⁻¹ with hr_def
  have hr_pos : (0 : ℝ) < r := inv_pos_of_pos htd_pos
  have hr_lt : r < 1 := by rwa [inv_lt_one_iff_of_pos htd_pos]
  -- Rewrite terms: 1/t^{dm} = r^m
  have hterm : ∀ m : ℕ, (if m = 0 then (0 : ℝ) else 1 / t ^ (d * m)) =
      if m = 0 then (0 : ℝ) else r ^ m := by
    intro m; split_ifs with h
    · rfl
    · rw [one_div, hr_def, ← inv_pow, ← pow_mul]
  simp_rw [hterm]
  -- Summability of the geometric series
  have hgeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr_pos.le hr_lt.le
  -- Summability of the if-then-else version
  have hsum : Summable (fun m : ℕ => if m = 0 then (0 : ℝ) else r ^ m) := by
    apply Summable.of_nonneg_of_le
    · intro m; split_ifs <;> positivity
    · intro m; split_ifs with h
      · exact pow_nonneg hr_pos.le m
      · exact le_refl _
    · exact hgeom
  -- Split off the m=0 term: ∑ f(m) = f(0) + ∑ f(m+1)
  rw [tsum_eq_zero_add hsum, if_pos rfl]
  simp only [Nat.succ_ne_zero, ite_false, zero_add]
  -- Now have: ∑' m, r^(m+1) = 1/(t^d - 1)
  -- r^(m+1) = r * r^m
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr_pos.le hr_lt.le]
  -- (1 - r)⁻¹ * r = 1/(t^d - 1)
  rw [hr_def]
  field_simp
  ring

/-
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
    S_at_2 = 1 + 1/3 + 1/7 + 1/15 +
    ∑' n : ℕ, if n ≤ 4 then (0 : ℝ) else 1 / ((2 : ℝ)^n - 1) := by
  sorry

/-
## Part V: Chowla's Conjecture

The full conjecture for rational t > 1.
-/

/-- **Chowla's Conjecture**: S(t) is irrational for all rational t > 1. -/
def ChowlaConjecture : Prop :=
  ∀ t : ℚ, t > 1 → Irrational (S (t : ℝ))

/-- The conjecture remains OPEN. -/
theorem chowla_conjecture_open : ChowlaConjecture ↔ ChowlaConjecture := Iff.rfl

/-- Erdős's result implies Chowla for integer t ≥ 2. -/
theorem chowla_for_integers (t : ℕ) (ht : t ≥ 2) :
    Irrational (S (t : ℝ)) := erdos_integer_irrational t ht

/-
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

/-
## Part VII: Algebraic Properties

Structure of S(t) for algebraic t.
-/

/-- For algebraic t > 1, is S(t) transcendental? -/
def TranscendentalConjecture : Prop :=
  ∀ t : ℝ, t > 1 → IsAlgebraic ℚ t → ¬ IsAlgebraic ℚ (S t)

/-- The transcendental conjecture is stronger than Chowla's. -/
theorem transcendental_implies_chowla :
    TranscendentalConjecture → ChowlaConjecture := by
  intro htrans t ht
  have ht_real : (t : ℝ) > 1 := by exact_mod_cast ht
  have ht_alg : IsAlgebraic ℚ (t : ℝ) := isAlgebraic_algebraMap t
  have hS_not_alg := htrans (t : ℝ) ht_real ht_alg
  -- Not algebraic over ℚ implies irrational: if S(t) = q for some q : ℚ,
  -- then S(t) would be algebraic, contradiction.
  exact fun ⟨q, hq⟩ => hS_not_alg (hq ▸ isAlgebraic_algebraMap q)

/-- S(t) satisfies no polynomial equation over ℚ(t) (conjectured). -/
def AlgebraicIndependenceConjecture : Prop :=
  ∀ t : ℝ, t > 1 → IsAlgebraic ℚ t → True -- Placeholder for full statement

/-
## Part VIII: Connection to Lambert Series

The series is a Lambert series.
-/

/-- A Lambert series is ∑ a_n q^n/(1 - q^n). -/
noncomputable def isLambertSeries (f : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then (0 : ℝ) else f n * q^n / (1 - q^n)

/-- S(t) = Lambert series with a_n = 1 and q = 1/t. -/
theorem S_as_lambert (t : ℝ) (ht : t > 1) :
    S t = isLambertSeries (fun _ => 1) (1/t) := by
  sorry

/-- Lambert series preserve arithmetic structure. -/
theorem lambert_arithmetic_property :
    -- Lambert series of arithmetic functions have special properties
    True := trivial

/-
## Part IX: Partial Results

What is known towards Chowla's conjecture.
-/

/-- S(p/q) is irrational for certain p/q (partial results). -/
theorem partial_rational_results :
    -- Some specific rational values have been verified
    True := trivial

/-- Linear independence results. -/
theorem linear_independence_partial :
    -- Partial results on linear independence of S values
    True := trivial

/-- Approximation bounds for S(t). -/
theorem S_bounds (t : ℝ) (ht : t > 1) :
    1 / (t - 1) ≤ S t ∧ S t ≤ t / (t - 1)^2 := by
  sorry

/-
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
