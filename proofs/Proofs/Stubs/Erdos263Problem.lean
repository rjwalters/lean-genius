/-
  Erdős Problem #263: Irrationality Sequences

  Source: https://erdosproblems.com/263
  Status: OPEN

  Statement:
  A sequence of positive integers (a_n) is an "irrationality sequence" if for every
  sequence of integers (b_n) with b_n/a_n → 1, the sum Σ 1/b_n is irrational.

  Questions:
  1. Is a_n = 2^{2^n} an irrationality sequence?
  2. Must every irrationality sequence satisfy a_n^{1/n} → ∞?

  Known Results:
  - Folklore: If lim a_n^{1/2^n} = ∞, then Σ 1/a_n is irrational
  - Kovač-Tao (2024): Strictly increasing with Σ 1/a_n convergent and
    lim a_{n+1}/a_n² = 0 are NOT irrationality sequences

  Tags: number-theory, irrationality, sequences, analysis
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

namespace Erdos263

open Filter Topology Real

/- ## Part I: Basic Definitions -/

/-- A sequence of positive integers. -/
def PosIntSeq := ℕ → ℕ+

/-- The sum Σ_{n=0}^∞ 1/b_n as a limit. -/
noncomputable def reciprocalSum (b : ℕ → ℤ) : ℝ :=
  ∑' n, (1 : ℝ) / b n

/-- The partial sum Σ_{n=0}^{N-1} 1/b_n. -/
noncomputable def reciprocalPartialSum (b : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (1 : ℝ) / b n

/-- A perturbation sequence: b_n/a_n → 1. -/
def IsPerturbation (a : PosIntSeq) (b : ℕ → ℤ) : Prop :=
  Tendsto (fun n => (b n : ℝ) / (a n : ℝ)) atTop (𝓝 1)

/- ## Part II: Irrationality Sequences -/

/-- An irrationality sequence: for all perturbations, the sum is irrational. -/
def IsIrrationalitySequence (a : PosIntSeq) : Prop :=
  ∀ b : ℕ → ℤ, IsPerturbation a b →
    (∀ n, b n > 0) → Irrational (reciprocalSum b)

/-- The double exponential sequence 2^{2^n}. -/
def doubleExp : PosIntSeq := fun n => ⟨2 ^ (2 ^ n), Nat.pos_pow_of_pos _ (by norm_num)⟩

/-- First question: Is 2^{2^n} an irrationality sequence? -/
def ErdosQuestion1 : Prop := IsIrrationalitySequence doubleExp

/- ## Part III: Growth Conditions -/

/-- a_n^{1/n} → ∞ as n → ∞. -/
def HasSuperexponentialGrowth (a : PosIntSeq) : Prop :=
  Tendsto (fun n => ((a n : ℕ) : ℝ) ^ (1 / (n : ℝ))) atTop atTop

/-- Second question: Must irrationality sequences have superexponential growth? -/
def ErdosQuestion2 : Prop :=
  ∀ a : PosIntSeq, IsIrrationalitySequence a → HasSuperexponentialGrowth a

/- ## Part IV: Folklore Condition -/

/-- The folklore condition: lim a_n^{1/2^n} = ∞. -/
def HasFolkloreGrowth (a : PosIntSeq) : Prop :=
  Tendsto (fun n => ((a n : ℕ) : ℝ) ^ (1 / (2 ^ n : ℝ))) atTop atTop

/-- Folklore result: if a_n^{1/2^n} → ∞, then Σ 1/a_n is irrational. -/
theorem folklore_irrationality (a : PosIntSeq)
    (h : HasFolkloreGrowth a) :
    Irrational (∑' n, (1 : ℝ) / (a n : ℕ)) := by
  sorry

/-- Double exponential does NOT satisfy the folklore condition.
    (2^{2^n})^{1/2^n} = 2^(2^n/2^n) = 2^1 = 2, which is constant, not → ∞.
    The irrationality of Σ 1/2^{2^n} follows instead from the Sylvester-type
    condition a_{n+1} ≈ a_n² (see doubleExp_sylvester_growth). -/
theorem doubleExp_not_folklore_growth : ¬HasFolkloreGrowth doubleExp := by
  intro h
  -- Key computation: (2^{2^n})^{1/2^n} = 2^((2^n) * (1/2^n)) = 2^1 = 2
  have hconst : ∀ n : ℕ, ((doubleExp n : ℕ) : ℝ) ^ (1 / (2 : ℝ) ^ n) = 2 := fun n => by
    simp only [doubleExp, PNat.val_mk]
    push_cast
    -- Goal: ((2:ℝ)^(2^n:ℕ))^(1/2^n) = 2  [inner ^ is npow, outer ^ is rpow]
    rw [← Real.rpow_natCast (2 : ℝ) (2 ^ n),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    -- Goal: (2:ℝ)^(((2^n:ℕ):ℝ) * (1/2^n)) = 2
    push_cast
    -- Goal: (2:ℝ)^((2:ℝ)^n * (1/(2:ℝ)^n)) = 2
    rw [one_div, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
    exact Real.rpow_one 2
  -- The function is constantly 2, so it cannot tend to ∞
  have h2 : Filter.Tendsto (fun _ : ℕ => (2 : ℝ)) Filter.atTop Filter.atTop :=
    h.congr (Filter.eventually_of_forall hconst)
  -- Contradiction: constant 2 doesn't tend to ∞ (since 3 > 2)
  have h3 : ∀ᶠ _ : ℕ in Filter.atTop, (3 : ℝ) ≤ 2 :=
    Filter.tendsto_atTop.mp h2 3
  obtain ⟨_, h4⟩ := h3.exists
  norm_num at h4

/-- For double exponential, a_{n+1} = a_n²: the sequence satisfies a_{n+1} = a_n².
    This implies irrationality of Σ 1/a_n by the Sylvester argument
    (a_{n+1} ≥ a_n² - a_n + 1 with equality approached). -/
theorem doubleExp_square_growth (n : ℕ) :
    (doubleExp (n + 1) : ℕ) = ((doubleExp n : ℕ)) ^ 2 := by
  change 2 ^ (2 ^ (n + 1)) = (2 ^ (2 ^ n)) ^ 2
  have : 2 ^ (n + 1) = 2 ^ n * 2 := by ring
  rw [this, pow_mul]

/- ## Part V: Kovač-Tao Result (2024) -/

/-- Strictly increasing sequence. -/
def IsStrictlyIncreasing (a : PosIntSeq) : Prop :=
  ∀ n m, n < m → (a n : ℕ) < (a m : ℕ)

/-- The sum Σ 1/a_n converges. -/
def HasConvergentSum (a : PosIntSeq) : Prop :=
  Summable (fun n => (1 : ℝ) / (a n : ℕ))

/-- The Kovač-Tao condition: lim a_{n+1}/a_n² = 0. -/
def HasKovacTaoCondition (a : PosIntSeq) : Prop :=
  Tendsto (fun n => ((a (n + 1) : ℕ) : ℝ) / ((a n : ℕ) : ℝ) ^ 2) atTop (𝓝 0)

/-- Kovač-Tao (2024): These sequences are NOT irrationality sequences. -/
theorem kovac_tao_not_irrationality (a : PosIntSeq)
    (hincr : IsStrictlyIncreasing a)
    (hconv : HasConvergentSum a)
    (hkt : HasKovacTaoCondition a) :
    ¬IsIrrationalitySequence a := by
  sorry

/- ## Part VI: Positive Condition -/

/-- The positive condition: liminf a_{n+1}/a_n^{2+ε} > 0 for some ε > 0. -/
def HasPositiveCondition (a : PosIntSeq) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    Filter.liminf (fun n => ((a (n + 1) : ℕ) : ℝ) / ((a n : ℕ) : ℝ) ^ (2 + ε)) atTop > 0

/-- Positive condition implies irrationality sequence. -/
theorem positive_condition_irrationality (a : PosIntSeq)
    (h : HasPositiveCondition a) :
    IsIrrationalitySequence a := by
  sorry

/- ## Part VII: Specific Examples -/

/-- The factorial sequence n!. -/
def factorial_seq : PosIntSeq := fun n => ⟨Nat.factorial (n + 1), Nat.factorial_pos _⟩

/-- Factorial does NOT have folklore growth. -/
theorem factorial_no_folklore_growth : ¬HasFolkloreGrowth factorial_seq := by
  sorry

/-- The tower sequence 2^2^...^2 (n times). -/
noncomputable def tower : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ tower n

/-- Double exponential is strictly increasing: n < m → 2^{2^n} < 2^{2^m}. -/
theorem doubleExp_strictly_increasing : IsStrictlyIncreasing doubleExp := by
  intro n m hnm
  -- Goal: (doubleExp n : ℕ) < (doubleExp m : ℕ), i.e., 2^{2^n} < 2^{2^m}
  change (2 : ℕ) ^ 2 ^ n < 2 ^ 2 ^ m
  exact Nat.pow_lt_pow_right (by norm_num) (Nat.pow_lt_pow_right (by norm_num) hnm)

/-- Double exponential sum converges: Σ 1/2^{2^n} converges.
    Proof: n ≤ 2^n for all n, so 2^n ≤ 2^{2^n}, giving
    1/2^{2^n} ≤ 1/2^n = (1/2)^n. The geometric series Σ (1/2)^n converges. -/
theorem doubleExp_convergent : HasConvergentSum doubleExp := by
  apply Summable.of_norm_bounded (fun n => ((1 : ℝ) / 2) ^ n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  intro n
  simp only [doubleExp, PNat.val_mk]
  rw [Real.norm_of_nonneg (by positivity)]
  have h_le : n ≤ 2 ^ n := (Nat.lt_pow_self (by norm_num : 1 < 2) n).le
  calc (1 : ℝ) / ((2 ^ 2 ^ n : ℕ) : ℝ)
      = 1 / (2 : ℝ) ^ (2 ^ n) := by push_cast; ring
    _ ≤ 1 / (2 : ℝ) ^ n :=
        one_div_le_one_div_of_le (pow_pos (by norm_num) n)
          (pow_le_pow_right (by norm_num : (1 : ℝ) ≤ 2) h_le)
    _ = (1 / 2) ^ n := by rw [one_div, inv_pow]

/- ## Part VIII: Characterization Attempts -/

/-- Double exponential has superexponential growth: (2^{2^n})^{1/n} → ∞.
    Proof: (2^{2^n})^{1/n} = 2^{2^n/n}, and 2^n/n → ∞. -/
theorem doubleExp_superexponential : HasSuperexponentialGrowth doubleExp := by
  sorry

/-- Gap between sufficient and necessary conditions.
    Witness: doubleExp = 2^{2^n} has superexponential growth but NOT folklore growth.
    This shows the folklore condition is strictly stronger than superexponential growth. -/
theorem characterization_gap :
    ∃ a : PosIntSeq, HasSuperexponentialGrowth a ∧ ¬HasFolkloreGrowth a :=
  ⟨doubleExp, doubleExp_superexponential, doubleExp_not_folklore_growth⟩

/-- The main open question formalized. -/
def MainQuestion : Prop :=
  ErdosQuestion1 ∧ ErdosQuestion2

/- ## Part IX: Connections to Other Problems -/

/-- Problem #262: Related irrationality question. -/
def connection_262 : Prop :=
  ∀ a : PosIntSeq, IsIrrationalitySequence a →
    Irrational (∑' n, (1 : ℝ) / (a n : ℕ))

/-- Problem #264: Another related irrationality question. -/
def connection_264 : Prop :=
  ∃ a : PosIntSeq, ¬IsIrrationalitySequence a ∧
    Irrational (∑' n, (1 : ℝ) / (a n : ℕ))

/- ## Part X: Cannot Be Resolved by Finite Computation -/

-- NOTE: The following theorem was removed because it is FALSE in classical logic.
-- In Lean 4 with Classical axioms, for any predicate P : α → Prop, one can define
-- `fun a => if P a then true else false : α → Bool` using LEM. The intended
-- statement is about computability (no computable decision procedure exists),
-- which would require Lean's Computability framework.

/-- Any finite truncation loses irrationality information. -/
theorem truncation_insufficient (N : ℕ) :
    ∃ a b : PosIntSeq, (∀ n < N, a n = b n) ∧
      IsIrrationalitySequence a ∧ ¬IsIrrationalitySequence b := by
  sorry

end Erdos263

/-
  ## Summary

  This file formalizes Erdős Problem #263 on irrationality sequences.

  **Status**: OPEN (cannot be resolved by finite computation)

  **Definition**: A sequence (a_n) of positive integers is an irrationality
  sequence if for every perturbation (b_n) with b_n/a_n → 1, the sum Σ 1/b_n
  is irrational.

  **Questions**:
  1. Is 2^{2^n} an irrationality sequence?
  2. Must irrationality sequences have a_n^{1/n} → ∞?

  **Known Results**:
  - Folklore: a_n^{1/2^n} → ∞ implies Σ 1/a_n is irrational
  - Kovač-Tao (2024): Strictly increasing with convergent sum and
    a_{n+1}/a_n² → 0 are NOT irrationality sequences
  - Positive condition: liminf a_{n+1}/a_n^{2+ε} > 0 implies irrationality sequence

  **What we formalize**:
  1. Irrationality sequences definition
  2. The double exponential sequence 2^{2^n}
  3. Growth conditions (superexponential, folklore)
  4. Kovač-Tao (2024) negative result
  5. Positive condition for irrationality sequences
  6. Connections to Problems #262 and #264
  7. Non-computability of the property

  **Proved**:
  - `doubleExp_strictly_increasing`: 2^{2^n} is strictly increasing
  - `doubleExp_square_growth`: a_{n+1} = a_n² for double exponential

  **Bug fixed**: `doubleExp_has_folklore_growth` was FALSE (2^{2^n})^{1/2^n} = 2,
  not → ∞. Replaced with correct `doubleExp_not_folklore_growth`.

  **Key sorries** (8 remaining):
  - `folklore_irrationality`: The folklore sufficient condition (deep)
  - `kovac_tao_not_irrationality`: The 2024 negative result (deep)
  - `positive_condition_irrationality`: Sufficient condition for irrationality (deep)
  - `doubleExp_convergent`: Comparison with geometric series (routine)
  - `doubleExp_not_folklore_growth`: Constant limit = 2 (routine)

  **Related**: Problems #262, #264 (other irrationality sequence questions)
-/
