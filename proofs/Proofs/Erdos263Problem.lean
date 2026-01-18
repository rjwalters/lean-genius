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

/-- Double exponential satisfies folklore condition. -/
theorem doubleExp_has_folklore_growth : HasFolkloreGrowth doubleExp := by
  sorry

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

/-- Double exponential is strictly increasing. -/
theorem doubleExp_strictly_increasing : IsStrictlyIncreasing doubleExp := by
  sorry

/-- Double exponential sum converges (rapidly). -/
theorem doubleExp_convergent : HasConvergentSum doubleExp := by
  sorry

/- ## Part VIII: Characterization Attempts -/

/-- Gap between sufficient and necessary conditions. -/
theorem characterization_gap :
    ∃ a : PosIntSeq, HasSuperexponentialGrowth a ∧ ¬HasFolkloreGrowth a := by
  sorry

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

/-- Irrationality is a global property requiring infinite information. -/
theorem irrationality_not_finitely_decidable :
    ¬∃ (decide : (ℕ → ℕ+) → Bool),
      ∀ a, decide a = true ↔ IsIrrationalitySequence a := by
  sorry

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

  **Key sorries**:
  - `folklore_irrationality`: The folklore sufficient condition
  - `kovac_tao_not_irrationality`: The 2024 negative result
  - `positive_condition_irrationality`: Sufficient condition for irrationality

  **Related**: Problems #262, #264 (other irrationality sequence questions)
-/
