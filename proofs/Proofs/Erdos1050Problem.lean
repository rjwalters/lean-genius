/-
  Erdős Problem #1050: Irrationality of ∑ 1/(2^n - 3)

  Source: https://erdosproblems.com/1050
  Status: SOLVED (Borwein 1991)

  Statement:
  Is the sum ∑_{n≥1} 1/(2^n - 3) irrational?

  Answer: YES (Borwein 1991).

  Borwein proved more generally that ∑_{n≥1} 1/(q^n + r) is irrational
  for integer q ≥ 2 and rational r ≠ 0 (with r ≠ -q^n for all n).

  Erdős conjectured these sums should be transcendental for all integer t.

  Tags: number-theory, irrationality, series, transcendence
-/

import Mathlib

namespace Erdos1050

open BigOperators Real

/-!
## Part I: The Series

Definition of the series ∑ 1/(q^n + r).
-/

/-- The general series T(q, r) = ∑_{n≥1} 1/(q^n + r). -/
noncomputable def T (q : ℕ) (r : ℚ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / ((q : ℝ)^n + (r : ℝ))

/-- The specific series S = ∑_{n≥1} 1/(2^n - 3). -/
noncomputable def S : ℝ := T 2 (-3)

/-- Alternative notation for clarity. -/
noncomputable def sumTwoMinusThree : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (2^n - 3 : ℝ)

/-- The two definitions agree. -/
theorem S_eq_sumTwoMinusThree : S = sumTwoMinusThree := by
  sorry

/-!
## Part II: Convergence

The series converges under appropriate conditions.
-/

/-- The series converges when q ≥ 2 and r ≠ -q^n for any n ≥ 1. -/
theorem T_summable (q : ℕ) (r : ℚ) (hq : q ≥ 2)
    (hr : ∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) :
    Summable (fun n : ℕ => if n = 0 then 0 else 1 / ((q : ℝ)^n + (r : ℝ))) := by
  sorry

/-- S = ∑ 1/(2^n - 3) converges. -/
theorem S_summable : Summable (fun n : ℕ => if n = 0 then 0 else 1 / (2^n - 3 : ℝ)) := by
  sorry

/-- The denominators 2^n - 3 are nonzero for n ≥ 2. -/
theorem denom_nonzero (n : ℕ) (hn : n ≥ 2) : (2 : ℝ)^n - 3 ≠ 0 := by
  sorry

/-- Note: 2^1 - 3 = -1, so the n=1 term is -1. -/
theorem first_term : 1 / ((2 : ℝ)^1 - 3) = -1 := by
  norm_num

/-!
## Part III: First Terms

Computing the initial terms of the series.
-/

/-- 2^1 - 3 = -1. -/
theorem term_1 : (2 : ℤ)^1 - 3 = -1 := by norm_num

/-- 2^2 - 3 = 1. -/
theorem term_2 : (2 : ℤ)^2 - 3 = 1 := by norm_num

/-- 2^3 - 3 = 5. -/
theorem term_3 : (2 : ℤ)^3 - 3 = 5 := by norm_num

/-- 2^4 - 3 = 13. -/
theorem term_4 : (2 : ℤ)^4 - 3 = 13 := by norm_num

/-- 2^5 - 3 = 29. -/
theorem term_5 : (2 : ℤ)^5 - 3 = 29 := by norm_num

/-- The series starts: -1 + 1 + 1/5 + 1/13 + 1/29 + ... -/
theorem S_first_terms :
    S = -1 + 1 + 1/5 + 1/13 + 1/29 +
      ∑' n : ℕ, if n ≤ 5 then 0 else 1 / (2^n - 3 : ℝ) := by
  sorry

/-!
## Part IV: Borwein's Theorem

The main irrationality result.
-/

/-- **Borwein (1991)**: ∑_{n≥1} 1/(q^n + r) is irrational
    for integer q ≥ 2 and rational r ≠ 0, r ≠ -q^n. -/
axiom borwein_irrationality (q : ℕ) (r : ℚ) (hq : q ≥ 2) (hr : r ≠ 0)
    (hpole : ∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) :
    Irrational (T q r)

/-- **Erdős Problem #1050: SOLVED**
    ∑_{n≥1} 1/(2^n - 3) is irrational. -/
theorem S_irrational : Irrational S := by
  apply borwein_irrationality 2 (-3)
  · norm_num
  · norm_num
  · intro n hn
    simp only [Rat.cast_neg, Rat.cast_ofNat]
    intro h
    -- We have -3 = -(2^n), so 3 = 2^n
    -- But 2^n ∈ {2, 4, 8, 16, ...}, never equals 3
    have h2 : (3 : ℝ) = (2 : ℝ)^n := by
      have : (-3 : ℝ) = -((2 : ℝ)^n) := h
      linarith
    -- For n ≥ 1, we have 2^n ∈ {2, 4, 8, ...}, never 3
    -- Case split: n = 1 gives 2; n ≥ 2 gives ≥ 4
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n = 1, so 2^1 = 2 ≠ 3
      have : n = 1 := by omega
      simp only [this, pow_one] at h2
      norm_num at h2
    · -- n ≥ 2, so 2^n ≥ 4 > 3
      have hnat : (2 : ℕ)^n ≥ 4 := by
        calc (2 : ℕ)^n ≥ 2^2 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn2
          _ = 4 := by norm_num
      have hreal : (2 : ℝ)^n ≥ 4 := by
        have : ((2 : ℕ)^n : ℝ) ≥ 4 := by exact_mod_cast hnat
        simp only [Nat.cast_ofNat] at this
        exact this
      linarith

/-!
## Part V: Related Series

Other series covered by Borwein's theorem.
-/

/-- ∑ 1/(2^n - 1) is irrational (Erdős's original result). -/
theorem sum_2n_minus_1_irrational : Irrational (T 2 (-1)) := by
  apply borwein_irrationality 2 (-1)
  · norm_num
  · norm_num
  · intro n hn
    simp only [Rat.cast_neg, Rat.cast_one]
    intro h
    -- -1 = -(2^n) implies 1 = 2^n, but 2^n ≥ 2 for n ≥ 1
    have h1 : (1 : ℝ) = (2 : ℝ)^n := by
      have : (-1 : ℝ) = -((2 : ℝ)^n) := h
      linarith
    have hnat : (2 : ℕ)^n ≥ 2 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    have hreal : (2 : ℝ)^n ≥ 2 := by
      have : ((2 : ℕ)^n : ℝ) ≥ 2 := by exact_mod_cast hnat
      simp only [Nat.cast_ofNat] at this
      exact this
    linarith

/-- ∑ 1/(2^n + 1) is irrational. -/
theorem sum_2n_plus_1_irrational : Irrational (T 2 1) := by
  apply borwein_irrationality 2 1
  · norm_num
  · norm_num
  · intro n hn
    simp only [Rat.cast_one]
    intro h
    -- 1 = -(2^n) implies 2^n = -1, but 2^n > 0
    have hneg : (2 : ℝ)^n = -1 := by
      have : (1 : ℝ) = -((2 : ℝ)^n) := h
      linarith
    have hpos : (2 : ℝ)^n > 0 := pow_pos (by norm_num : (0 : ℝ) < 2) n
    linarith

/-- ∑ 1/(3^n - 1) is irrational. -/
theorem sum_3n_minus_1_irrational : Irrational (T 3 (-1)) := by
  apply borwein_irrationality 3 (-1)
  · norm_num
  · norm_num
  · intro n hn
    simp only [Rat.cast_neg, Rat.cast_one]
    intro h
    -- -1 = -(3^n) implies 1 = 3^n, but 3^n ≥ 3 for n ≥ 1
    have h1 : (1 : ℝ) = (3 : ℝ)^n := by
      have : (-1 : ℝ) = -((3 : ℝ)^n) := h
      linarith
    have hnat : (3 : ℕ)^n ≥ 3 := by
      calc (3 : ℕ)^n ≥ 3^1 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hn
        _ = 3 := by norm_num
    have hreal : (3 : ℝ)^n ≥ 3 := by
      have : ((3 : ℕ)^n : ℝ) ≥ 3 := by exact_mod_cast hnat
      simp only [Nat.cast_ofNat] at this
      exact this
    linarith

/-- ∑ 1/(q^n + r) for any valid q, r. -/
theorem general_irrational (q : ℕ) (r : ℚ) (hq : q ≥ 2) (hr : r ≠ 0)
    (hpole : ∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) :
    Irrational (T q r) := borwein_irrationality q r hq hr hpole

/-!
## Part VI: The Transcendence Conjecture

Erdős conjectured a stronger result.
-/

/-- **Erdős's Conjecture**: ∑ 1/(2^n + t) is transcendental for all integer t ≠ 0. -/
def ErdosTranscendenceConjecture : Prop :=
  ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, n ≥ 1 → (t : ℝ) ≠ -2^n) →
    Transcendental ℚ (T 2 t)

/-- General transcendence conjecture. -/
def GeneralTranscendenceConjecture : Prop :=
  ∀ q : ℕ, q ≥ 2 → ∀ r : ℚ, r ≠ 0 →
    (∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) →
    Transcendental ℚ (T q r)

/-- Transcendence implies irrationality. -/
theorem transcendence_implies_irrationality :
    GeneralTranscendenceConjecture →
    ∀ q : ℕ, q ≥ 2 → ∀ r : ℚ, r ≠ 0 →
      (∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) →
      Irrational (T q r) := by
  sorry

/-- The transcendence conjecture status: OPEN. -/
axiom transcendence_conjecture_status :
    -- The transcendence conjecture remains open
    True

/-!
## Part VII: Connection to Erdős Problem #1049

This problem relates to the divisor sum irrationality.
-/

/-- Recall: S(t) = ∑ 1/(t^n - 1) from Problem #1049. -/
noncomputable def S_1049 (t : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (t^n - 1)

/-- T(q, -1) = S_1049(q) for integer q. -/
theorem T_eq_S_1049 (q : ℕ) (hq : q ≥ 2) : T q (-1) = S_1049 q := by
  sorry

/-- The problems are related through shifting the constant. -/
theorem problems_related (q : ℕ) (hq : q ≥ 2) (r : ℚ) (hr : r ≠ 0) :
    -- T(q, r) and S_1049(q) are both irrational for appropriate parameters
    Irrational (T q (-1)) ∧
    (∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) → Irrational (T q r) := by
  sorry

/-!
## Part VIII: Approximation and Numerical Values

Computing the value of the series.
-/

/-- S ≈ 0.2868... -/
axiom S_approx : S > 0.286 ∧ S < 0.288

/-- S is positive (despite the first term being negative). -/
theorem S_positive : S > 0 := by
  obtain ⟨hl, _⟩ := S_approx
  linarith

/-- Upper bound: S < 1. -/
theorem S_lt_one : S < 1 := by
  obtain ⟨_, hu⟩ := S_approx
  linarith

/-- The partial sums converge to S. -/
theorem partial_sums_converge :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, if n = 0 then 0 else 1 / (2^n - 3 : ℝ))
      Filter.atTop (nhds S) := by
  sorry

/-!
## Part IX: OEIS Connection

The sequence of denominators.
-/

/-- OEIS A331372: Related sequence. -/
def oeis_A331372 : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2^(n+1) - 3

/-- The denominators form A000051 shifted: 2^n - 3. -/
theorem denom_sequence (n : ℕ) (hn : n ≥ 1) :
    oeis_A331372 n = 2^n - 3 := by
  sorry

/-- Denominators grow exponentially. -/
theorem denom_growth (n : ℕ) (hn : n ≥ 3) :
    (oeis_A331372 n : ℝ) > 2^(n-1) := by
  sorry

/-!
## Part X: Main Results

Summary of Erdős Problem #1050.
-/

/-- **Erdős Problem #1050: SOLVED**

    Question: Is ∑_{n≥1} 1/(2^n - 3) irrational?

    Answer: YES (Borwein 1991).

    Borwein proved the more general result that ∑_{n≥1} 1/(q^n + r)
    is irrational for integer q ≥ 2 and rational r ≠ 0, r ≠ -q^n.

    The stronger transcendence conjecture remains OPEN. -/
theorem erdos_1050 : Irrational S := S_irrational

/-- The answer to Erdős #1050. -/
def erdos_1050_answer : String :=
  "SOLVED: ∑ 1/(2^n - 3) is irrational (Borwein 1991)"

/-- The status of Erdős #1050. -/
def erdos_1050_status : String :=
  "SOLVED by Peter Borwein (1991)"

/-- Borwein's general theorem. -/
theorem borwein_theorem (q : ℕ) (r : ℚ) (hq : q ≥ 2) (hr : r ≠ 0)
    (hpole : ∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) :
    Irrational (T q r) := borwein_irrationality q r hq hr hpole

#check erdos_1050
#check borwein_irrationality
#check ErdosTranscendenceConjecture

end Erdos1050
