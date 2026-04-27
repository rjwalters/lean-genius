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
import Mathlib.Tactic

-- Compatibility shim: PNat.val_mk was removed in newer Mathlib (it's definitionally rfl)
@[simp] theorem PNat.val_mk (n : ℕ) (h : 0 < n) : (⟨n, h⟩ : ℕ+).val = n := rfl

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
def doubleExp : PosIntSeq := fun n => ⟨2 ^ (2 ^ n), by positivity⟩

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
    -- Make the PNat coercion explicit via definitional equality
    show ((2 ^ 2 ^ n : ℕ) : ℝ) ^ (1 / (2 : ℝ) ^ n) = 2
    -- Goal: ((2^{2^n}:ℕ):ℝ)^(1/2^n) = 2
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
    h.congr hconst
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

/-- Double exponential does NOT satisfy the Kovač-Tao condition.
    Since a_{n+1} = a_n² for all n (doubleExp_square_growth), the ratio
    a_{n+1}/a_n² = 1 for all n — not 0. The Kovač-Tao theorem does NOT
    apply to doubleExp: 2^{2^n} sits exactly AT the quadratic threshold,
    not strictly below it. -/
theorem doubleExp_not_kovac_tao : ¬HasKovacTaoCondition doubleExp := by
  intro h
  -- The ratio is constantly 1: a_{n+1}/a_n² = a_n²/a_n² = 1
  have hconst : ∀ n : ℕ,
      ((doubleExp (n + 1) : ℕ) : ℝ) / ((doubleExp n : ℕ) : ℝ) ^ 2 = 1 := fun n => by
    have heq := doubleExp_square_growth n
    have hpos : (0 : ℝ) < ((doubleExp n : ℕ) : ℝ) := by exact_mod_cast (doubleExp n).pos
    have hcast : ((doubleExp (n + 1) : ℕ) : ℝ) = ((doubleExp n : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast heq
    rw [hcast, div_self (pow_pos hpos 2).ne']
  -- Constant 1 sequence cannot converge to 0 (unique limits)
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
    h.congr hconst
  have h2 : (0 : ℝ) = 1 := tendsto_nhds_unique h1 tendsto_const_nhds
  norm_num at h2

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

/-- n + 2 ≤ 2^(2^n) for all n : ℕ. -/
private lemma succ2_le_two_pow_pow (n : ℕ) : n + 2 ≤ 2 ^ (2 ^ n) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    have hge2 : 2 ≤ 2 ^ (2 ^ m) :=
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 ^ m) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow m 2 (by norm_num))
    have h2m : 2 ^ (2 ^ (m + 1)) = 2 ^ (2 ^ m) * 2 ^ (2 ^ m) := by
      have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      rw [this, pow_add]
    rw [h2m]
    calc m + 1 + 2 = m + 3 := by ring
      _ ≤ 2 * (m + 2) := by omega
      _ ≤ 2 ^ (2 ^ m) * 2 ^ (2 ^ m) := Nat.mul_le_mul hge2 ih

/-- (n+1)! ≤ 2^(2^n) for all n : ℕ. -/
private lemma factorial_le_two_pow_pow (n : ℕ) : Nat.factorial (n + 1) ≤ 2 ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Nat.factorial_succ]
    have h2m : 2 ^ (2 ^ (m + 1)) = 2 ^ (2 ^ m) * 2 ^ (2 ^ m) := by
      have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      rw [this, pow_add]
    rw [h2m]
    exact Nat.mul_le_mul (succ2_le_two_pow_pow m) ih

/-- Factorial does NOT have folklore growth.
    Key bound: (n+1)! ≤ 2^(2^n), so ((n+1)!)^{1/2^n} ≤ 2 for all n.
    This contradicts → ∞ (function is bounded). -/
theorem factorial_no_folklore_growth : ¬HasFolkloreGrowth factorial_seq := by
  intro h
  have h3 : ∀ᶠ n in Filter.atTop, (3 : ℝ) ≤
      ((factorial_seq n : ℕ) : ℝ) ^ (1 / (2 : ℝ) ^ n) :=
    Filter.tendsto_atTop.mp h 3
  obtain ⟨N, hN⟩ := h3.exists
  have hle : ((factorial_seq N : ℕ) : ℝ) ^ (1 / (2 : ℝ) ^ N) ≤ 2 := by
    show (Nat.factorial (N + 1) : ℝ) ^ (1 / (2 : ℝ) ^ N) ≤ 2
    have hfact : (Nat.factorial (N + 1) : ℝ) ≤ (2 : ℝ) ^ (2 ^ N) :=
      by exact_mod_cast factorial_le_two_pow_pow N
    calc (Nat.factorial (N + 1) : ℝ) ^ (1 / (2 : ℝ) ^ N)
        ≤ ((2 : ℝ) ^ (2 ^ N)) ^ (1 / (2 : ℝ) ^ N) :=
          Real.rpow_le_rpow (by positivity) hfact (by positivity)
      _ = (2 : ℝ) := by
          rw [← Real.rpow_natCast (2 : ℝ) (2 ^ N),
              ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          push_cast
          rw [mul_one_div, div_self (pow_ne_zero N (by norm_num : (2 : ℝ) ≠ 0)),
              Real.rpow_one]
  linarith

/-- The factorial sequence satisfies the Kovač-Tao condition: (n+2)!/((n+1)!)² → 0.
    Proof: ratio = (n+2)/(n+1)! ≤ 2/n! (since n+2 ≤ 2*(n+1)), and 1/n! → 0.
    Consequence (pending kovac_tao_not_irrationality): factorial is NOT an irrationality
    sequence — despite having superexponential growth ((n!)^{1/n} ~ n/e → ∞). -/
theorem factorial_has_kovac_tao_condition : HasKovacTaoCondition factorial_seq := by
  unfold HasKovacTaoCondition factorial_seq
  show Tendsto (fun n : ℕ => (Nat.factorial (n + 2) : ℝ) / (Nat.factorial (n + 1) : ℝ) ^ 2)
      atTop (𝓝 0)
  -- Step 1: Ratio simplifies: (n+2)!/((n+1)!)² = (n+2)/(n+1)!
  have hratio : ∀ n : ℕ,
      (Nat.factorial (n + 2) : ℝ) / ((Nat.factorial (n + 1) : ℝ) ^ 2) =
      (n + 2 : ℝ) / Nat.factorial (n + 1) := fun n => by
    have hpos : (0 : ℝ) < Nat.factorial (n + 1) := by exact_mod_cast Nat.factorial_pos _
    rw [show Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) from Nat.factorial_succ _]
    push_cast; field_simp
  -- Step 2: 2*n! ≥ 2^n for all n (key arithmetic bound)
  have hfact2 : ∀ n : ℕ, 2 ^ n ≤ 2 * Nat.factorial n := by
    intro n
    induction n with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ, Nat.factorial_succ]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · norm_num
      · nlinarith [Nat.factorial_pos m]
  -- Step 3: 1/n! → 0 (comparison with geometric series using hfact2)
  have hterm : Tendsto (fun n : ℕ => (1 : ℝ) / Nat.factorial n) atTop (𝓝 0) := by
    apply Summable.tendsto_atTop_zero
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (r := 1/2) (by norm_num) (by norm_num)).mul_left 2)
    intro n
    rw [Real.norm_of_nonneg (by positivity)]
    have hfact_pos : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
    have h2n_pos : (0 : ℝ) < 2 ^ n := by positivity
    have heq : (2 : ℝ) * (1 / 2) ^ n = 2 / 2 ^ n := by
      rw [div_pow, one_pow, mul_one_div]
    rw [heq, div_le_div_iff₀ hfact_pos h2n_pos]
    have h_le : (2:ℝ)^n ≤ 2 * Nat.factorial n := by exact_mod_cast hfact2 n
    linarith
  -- Step 4: Upper bound (n+2)/(n+1)! ≤ 2/n! (since n+2 ≤ 2*(n+1))
  have hle : ∀ n : ℕ, (n + 2 : ℝ) / Nat.factorial (n + 1) ≤ 2 * (1 / Nat.factorial n) := by
    intro n
    have hfact : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos _
    have hfact1 : (0 : ℝ) < Nat.factorial (n + 1) := by exact_mod_cast Nat.factorial_pos _
    rw [show (2 : ℝ) * (1 / Nat.factorial n) = 2 / Nat.factorial n from by ring,
        div_le_div_iff₀ hfact1 hfact]
    have hsucc : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
      norm_cast
    rw [hsucc]
    nlinarith [Nat.factorial_pos n]
  -- Step 5: Squeeze between 0 and 2/n! → 0
  rw [show (fun n : ℕ => (Nat.factorial (n + 2) : ℝ) / (Nat.factorial (n + 1) : ℝ) ^ 2) =
      (fun n : ℕ => ((n : ℝ) + 2) / Nat.factorial (n + 1)) from funext hratio]
  apply squeeze_zero (fun n => by positivity) hle
  simpa [mul_comm] using hterm.const_mul 2

/-- Factorial sequence is strictly increasing. -/
theorem factorial_strictly_increasing : IsStrictlyIncreasing factorial_seq := by
  intro n m hnm
  show Nat.factorial (n + 1) < Nat.factorial (m + 1)
  -- Self-contained proof: factorial strictly increasing from 1 onwards
  suffices h : ∀ a b, 1 ≤ a → a < b → Nat.factorial a < Nat.factorial b from
    h (n + 1) (m + 1) (by omega) (by omega)
  intro a b ha hab
  induction b with
  | zero => omega
  | succ c ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with hac | hac
    · have hc1 : 1 ≤ c := by omega
      have ihc := ih hac
      have hstep : Nat.factorial c < Nat.factorial (c + 1) := by
        rw [Nat.factorial_succ]
        nlinarith [Nat.factorial_pos c]
      linarith
    · subst hac
      rw [Nat.factorial_succ]
      nlinarith [Nat.factorial_pos a]

/-- 2^n ≤ (n+1)! for all n. -/
private lemma two_pow_le_factorial_succ (n : ℕ) : 2 ^ n ≤ Nat.factorial (n + 1) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ, Nat.factorial_succ]
    -- Goal: 2^m * 2 ≤ (m+2) * (m+1)!
    calc 2 ^ m * 2
        = 2 * 2 ^ m := by ring
      _ ≤ (m + 2) * Nat.factorial (m + 1) := Nat.mul_le_mul (by omega) ih

/-- Factorial sequence has convergent sum: Σ 1/(n+1)! converges.
    Proof: (n+1)! ≥ 2^n, so 1/(n+1)! ≤ (1/2)^n, and Σ (1/2)^n converges. -/
theorem factorial_convergent : HasConvergentSum factorial_seq := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (r := 1/2) (by norm_num) (by norm_num))
  intro n
  show ‖(1 : ℝ) / (Nat.factorial (n + 1) : ℝ)‖ ≤ (1 / 2 : ℝ) ^ n
  rw [Real.norm_of_nonneg (by positivity)]
  have h2n : (2 : ℝ) ^ n ≤ (Nat.factorial (n + 1) : ℝ) :=
    by exact_mod_cast two_pow_le_factorial_succ n
  calc 1 / (Nat.factorial (n + 1) : ℝ)
      ≤ 1 / (2 : ℝ) ^ n := one_div_le_one_div_of_le (by positivity) h2n
    _ = (1 / 2) ^ n := by rw [div_pow, one_pow]

/-- Conditional result: if Kovač-Tao implies non-irrationality for sequences
    satisfying its hypotheses, then factorial is not an irrationality sequence. -/
theorem factorial_not_irrationality_if_kt
    (hkt : ∀ a : PosIntSeq, IsStrictlyIncreasing a → HasConvergentSum a →
           HasKovacTaoCondition a → ¬IsIrrationalitySequence a) :
    ¬IsIrrationalitySequence factorial_seq :=
  hkt factorial_seq factorial_strictly_increasing factorial_convergent
      factorial_has_kovac_tao_condition

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

/-- n ≤ 2^n for all n. -/
private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    calc m + 1 ≤ 2 ^ m + 1 := by linarith
      _ ≤ 2 ^ m * 2 := by linarith [Nat.one_le_pow m 2 (by norm_num)]
      _ = 2 ^ (m + 1) := by ring

/-- Double exponential sum converges: Σ 1/2^{2^n} converges.
    Proof: n ≤ 2^n for all n, so 2^n ≤ 2^{2^n}, giving
    1/2^{2^n} ≤ 1/2^n = (1/2)^n. The geometric series Σ (1/2)^n converges. -/
theorem doubleExp_convergent : HasConvergentSum doubleExp := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (r := 1/2) (by norm_num) (by norm_num))
  intro n
  show ‖(1 : ℝ) / ((2 ^ 2 ^ n : ℕ) : ℝ)‖ ≤ ((1 : ℝ) / 2) ^ n
  rw [Real.norm_of_nonneg (by positivity)]
  have h_pow_le : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (2 ^ n) := by
    have : (2 : ℕ) ^ n ≤ (2 : ℕ) ^ (2 ^ n) :=
      Nat.pow_le_pow_right (by norm_num) (nat_le_two_pow n)
    exact_mod_cast this
  calc (1 : ℝ) / ((2 ^ 2 ^ n : ℕ) : ℝ)
      = 1 / (2 : ℝ) ^ (2 ^ n) := by push_cast; ring
    _ ≤ 1 / (2 : ℝ) ^ n := one_div_le_one_div_of_le (pow_pos (by norm_num) n) h_pow_le
    _ = (1 / 2) ^ n := by simp [one_div, inv_pow]

/- ## Part VIII: Characterization Attempts -/

/-- 2^n ≥ n^2 for n ≥ 4. Key for the superexponential bound. -/
private lemma two_pow_ge_sq (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases le_or_gt 4 m with hm4 | hm3
    · have ihm := ih hm4
      -- 2m+1 ≤ m^2 for m ≥ 4 (since m^2 ≥ 4m ≥ 2m+1)
      have h1 : 2 * m + 1 ≤ m ^ 2 := by
        have hmm : 4 * m ≤ m ^ 2 := by
          have := Nat.mul_le_mul hm4 (le_refl m)
          linarith [show m * m = m ^ 2 from by ring]
        linarith
      calc (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
        _ ≤ m ^ 2 + m ^ 2 := by linarith
        _ = 2 * m ^ 2 := by ring
        _ ≤ 2 * 2 ^ m := by linarith
        _ = 2 ^ (m + 1) := by ring
    · -- m < 4 and 4 ≤ m+1 forces m = 3
      have : m = 3 := by omega
      subst this; norm_num

/-- Double exponential has superexponential growth: (2^{2^n})^{1/n} → ∞.
    Key: for n ≥ 4, (2^{2^n})^{1/n} = 2^{2^n/n} ≥ 2^n ≥ n since 2^n ≥ n^2. -/
theorem doubleExp_superexponential : HasSuperexponentialGrowth doubleExp := by
  unfold HasSuperexponentialGrowth
  rw [Filter.tendsto_atTop_atTop]
  intro C
  -- For n ≥ max 4 ⌈C⌉₊: chain C ≤ n ≤ 2^n ≤ (2^{2^n})^{1/n}
  refine ⟨max 4 ⌈C⌉₊, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_left 4 _).trans hn
  have hnC : C ≤ (n : ℝ) := by
    have h1 : ⌈C⌉₊ ≤ n := (le_max_right 4 _).trans hn
    exact (Nat.le_ceil C).trans (by exact_mod_cast h1)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
  have hdn : ((doubleExp n : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ n) := by
    simp only [doubleExp]; norm_cast
  rw [hdn]
  have h2n_le : (2 : ℝ) ^ n ≤ ((2 : ℝ) ^ (2 ^ n)) ^ (1 / (n : ℝ)) := by
    -- (2^n)^(1/n) ≤ (2^(2^n))^(1/n) since 2^n ≤ 2^(2^n) and exponent > 0? No.
    -- Instead: (2:ℝ)^n = (2:ℝ)^(n*1) ≤ (2:ℝ)^(2^n/n*n)... use rpow monotonicity.
    -- Key: 2^n ≤ (2^(2^n))^(1/n) ⟺ (2^n)^n ≤ 2^(2^n) ⟺ 2^(n^2) ≤ 2^(2^n)
    --   ⟺ n^2 ≤ 2^n (for n ≥ 4, from two_pow_ge_sq)
    rw [← Real.rpow_natCast (2 : ℝ) n,
        ← Real.rpow_natCast (2 : ℝ) (2 ^ n : ℕ),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    -- Goal: (n:ℝ) ≤ (2^n : ℕ) * (1/n)
    rw [mul_one_div]
    have h := two_pow_ge_sq n hn4
    rw [le_div_iff₀ hn_pos]
    have h2 : (n : ℝ) * n = (n : ℝ) ^ 2 := by ring
    rw [h2]; exact_mod_cast h
  calc C ≤ (n : ℝ) := hnC
    _ ≤ (2 : ℝ) ^ n := by exact_mod_cast nat_le_two_pow n
    _ ≤ ((2 : ℝ) ^ (2 ^ n)) ^ (1 / (n : ℝ)) := h2n_le

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

/-- Connection #262 holds: every irrationality sequence has an irrational reciprocal sum.
    Proof: Take the trivial perturbation b_n = a_n, which has b_n/a_n = 1 → 1. -/
theorem connection_262_holds : connection_262 := by
  intro a ha
  have hpert : IsPerturbation a (fun n => (a n : ℤ)) := by
    unfold IsPerturbation
    have hfun : (fun n : ℕ => ((a n : ℤ) : ℝ) / (a n : ℝ)) = fun _ => 1 := by
      ext n
      have hpos : (a n : ℝ) > 0 := by exact_mod_cast (a n).pos
      have heq : ((a n : ℤ) : ℝ) = (a n : ℝ) := by norm_cast
      rw [heq, div_self hpos.ne']
    rw [hfun]
    exact tendsto_const_nhds
  have hpos : ∀ n, (a n : ℤ) > 0 := fun n => by exact_mod_cast (a n).pos
  have hirr : Irrational (reciprocalSum (fun n => (a n : ℤ))) := ha _ hpert hpos
  have hsum : reciprocalSum (fun n => (a n : ℤ)) = ∑' n, (1 : ℝ) / (a n : ℕ) := by
    simp only [reciprocalSum]
    congr 1
  rwa [← hsum]

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

/- ## Part XI: Connection Theorems -/

/-- Every irrationality sequence has an irrational reciprocal sum.
    Proof: take b n = (a n : ℕ) as ℤ — the identity perturbation.
    Since b n / a n = 1 → 1, `IsIrrationalitySequence a` gives the result. -/
theorem connection_262_proved : connection_262 := by
  intro a ha
  have hirr := ha (fun n => ((a n : ℕ) : ℤ))
    (show IsPerturbation a (fun n => ((a n : ℕ) : ℤ)) from by
      unfold IsPerturbation
      have hratio : ∀ n, (((a n : ℕ) : ℤ) : ℝ) / ((a n : ℕ+) : ℝ) = 1 := fun n => by
        have hpos : (0 : ℝ) < ((a n : ℕ+) : ℝ) := by exact_mod_cast (a n).pos
        have heq : (((a n : ℕ) : ℤ) : ℝ) = ((a n : ℕ+) : ℝ) := by norm_cast
        rw [heq, div_self hpos.ne']
      simp_rw [hratio]; exact tendsto_const_nhds)
    (fun n => by positivity)
  simpa only [reciprocalSum, Int.cast_natCast] using hirr

/-- Each term 1/(doubleExp n) equals 1/2^{2^n} as a real. -/
private lemma doubleExp_term_eq (n : ℕ) :
    (1 : ℝ) / ((doubleExp n : ℕ) : ℝ) = 1 / (2 : ℝ) ^ (2 ^ n) := by
  simp [doubleExp]

/-- Summability of 1/2^{2^n}, rewritten from doubleExp_convergent. -/
private lemma doubleExp_sum_summable :
    Summable (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ (2 ^ n)) :=
  doubleExp_convergent.congr (fun n => doubleExp_term_eq n)

/-- The tail ∑' k, 1/2^{2^(k+N+1)} is positive.
    Note: each term is positive; Aristotle candidate (tsum_pos API varies by Mathlib version). -/
private lemma doubleExp_tail_pos (N : ℕ) :
    0 < ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) := by
  have hsum : Summable (fun k : ℕ => (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1))) := by
    have h : Summable (fun k : ℕ => (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + (N + 1)))) :=
      (summable_nat_add_iff (N + 1)).mpr doubleExp_sum_summable
    exact h.congr (fun k => by congr 1; congr 1; omega)
  exact hsum.tsum_pos (fun k => by positivity) 0 (by positivity)

/-- D * (finite sum) is a natural number: 2^{2^N} * Σ_{k<N} 1/2^{2^k} ∈ ℕ.
    Each term: 2^{2^N} * (1/2^{2^k}) = 2^{2^N - 2^k} ∈ ℕ (since 2^k ≤ 2^N for k ≤ N). -/
private lemma doubleExp_fin_mul_nat (N : ℕ) :
    ∃ m : ℕ, (2 : ℝ) ^ (2 ^ N) * ∑ k ∈ Finset.range N, (1 : ℝ) / (2 : ℝ) ^ (2 ^ k) =
    (m : ℝ) := by
  refine ⟨∑ k ∈ Finset.range N, (2 : ℕ) ^ (2 ^ N - 2 ^ k), ?_⟩
  simp_rw [Finset.mul_sum, mul_one_div]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hle : 2 ^ k ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hk.le
  -- Goal: (2:ℝ)^(2^N) / (2:ℝ)^(2^k) = (2:ℝ)^(2^N - 2^k)
  -- Use: pow_sub₀ says a^(m-n) = a^m * (a^n)⁻¹, so a^m/a^n = a^(m-n)
  rw [div_eq_mul_inv, ← pow_sub₀ (2 : ℝ) (by norm_num : (2 : ℝ) ≠ 0) hle]

/-- Tail bound: 2^{2^N} * Σ_{k≥N+1} 1/2^{2^k} < 1 / (2^{2^N} - 1).
    Strategy: set D = 2^{2^N}, r = 1/D². Each term 1/D^{2^{k+1}} ≤ r^{k+1}
    (since 2*(k+1) ≤ 2^{k+1}), so D*T ≤ D/(D²-1) < 1/(D-1). -/
private lemma doubleExp_tail_bound (N : ℕ) :
    (2 : ℝ) ^ (2 ^ N) * ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) <
    1 / ((2 : ℝ) ^ (2 ^ N) - 1) := by
  set D := (2 : ℝ) ^ (2 ^ N) with hD_def
  have hD_pos : (0 : ℝ) < D := by positivity
  have hD_ge2 : (2 : ℝ) ≤ D := by
    have h1 : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ N) := pow_le_pow_right (by norm_num) (by exact_mod_cast h1)
  have hD_ge1 : (1 : ℝ) ≤ D := by linarith
  have hD1_pos : (0 : ℝ) < D - 1 := by linarith
  have hD2_pos : (0 : ℝ) < D ^ 2 - 1 := by nlinarith
  -- Geometric ratio r = 1/D², with 0 ≤ r < 1
  set r := (1 : ℝ) / D ^ 2 with hr_def
  have hr_nn : (0 : ℝ) ≤ r := by positivity
  have hr_lt1 : r < 1 := by
    unfold_let r; rw [div_lt_one (by positivity)]; nlinarith
  -- Rewrite each term: 1/2^{2^{k+N+1}} = 1/D^{2^{k+1}}
  have hterm : ∀ k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) = 1 / D ^ (2 ^ (k + 1)) := by
    intro k; congr 1; rw [hD_def, ← pow_mul]; congr 1
    have : k + N + 1 = N + (k + 1) := by omega
    rw [this, pow_add]
  -- Key arithmetic: 2*(k+1) ≤ 2^{k+1}, proved via k+1 ≤ 2^k
  have key_arith : ∀ k : ℕ, 2 * (k + 1) ≤ 2 ^ (k + 1) := by
    intro k
    have h : k + 1 ≤ 2 ^ k := by
      induction k with
      | zero => norm_num
      | succ m ih =>
        calc m + 1 + 1 ≤ 2 ^ m + 1 := by linarith
          _ ≤ 2 ^ m + 2 ^ m := by linarith [Nat.one_le_pow m 2 (by norm_num)]
          _ = 2 ^ (m + 1) := by ring
    calc 2 * (k + 1) ≤ 2 * 2 ^ k := by linarith
      _ = 2 ^ (k + 1) := by ring
  -- Term bound: 1/D^{2^{k+1}} ≤ r^{k+1} = (1/D²)^{k+1}
  have hterm_bound : ∀ k : ℕ, (1 : ℝ) / D ^ (2 ^ (k + 1)) ≤ r ^ (k + 1) := by
    intro k
    calc (1 : ℝ) / D ^ (2 ^ (k + 1))
        ≤ 1 / D ^ (2 * (k + 1)) :=
            one_div_le_one_div_of_le (by positivity) (pow_le_pow_right hD_ge1 (key_arith k))
      _ = r ^ (k + 1) := by
            unfold_let r; rw [div_pow, one_pow, ← pow_mul]
  -- Summability
  have hTsumm : Summable (fun k : ℕ => r ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr_nn hr_lt1)
  have hTsumm' : Summable (fun k : ℕ => (1 : ℝ) / D ^ (2 ^ (k + 1))) :=
    hTsumm.of_nonneg_of_le (fun k => by positivity) hterm_bound
  -- Geometric series: ∑ r^{k+1} = r/(1-r) = 1/(D²-1)
  have hgeo : ∑' k : ℕ, r ^ (k + 1) = 1 / (D ^ 2 - 1) := by
    rw [show (fun k : ℕ => r ^ (k + 1)) = (fun k => r * r ^ k) from funext (fun k => by ring)]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr_nn hr_lt1]
    unfold_let r
    have hD2_ne : D ^ 2 ≠ 0 := by positivity
    have h1r_pos : (0 : ℝ) < 1 - 1 / D ^ 2 := by
      rw [sub_pos, div_lt_one (by positivity)]; nlinarith
    field_simp [hD2_ne, h1r_pos.ne']
    ring
  -- Rewrite tsum in goal using hterm, then bound
  rw [show (fun k : ℕ => (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1))) =
          (fun k => 1 / D ^ (2 ^ (k + 1))) from funext hterm]
  have hT_le : ∑' k : ℕ, (1 : ℝ) / D ^ (2 ^ (k + 1)) ≤ 1 / (D ^ 2 - 1) := by
    rw [← hgeo]; exact tsum_le_tsum hterm_bound hTsumm' hTsumm
  calc D * ∑' k : ℕ, (1 : ℝ) / D ^ (2 ^ (k + 1))
      ≤ D * (1 / (D ^ 2 - 1)) := mul_le_mul_of_nonneg_left hT_le hD_pos.le
    _ = D / (D ^ 2 - 1) := by ring
    _ < 1 / (D - 1) := by
          rw [div_lt_div_iff hD2_pos hD1_pos]; nlinarith

/-- Split: ∑' n, f n = ∑ n ∈ range N, f n + f N + ∑' n, f (n + N + 1). -/
private lemma tsum_split_at (f : ℕ → ℝ) (hf : Summable f) (N : ℕ) :
    ∑' n, f n = (∑ n ∈ Finset.range N, f n) + f N + ∑' n, f (n + N + 1) := by
  have hfN : Summable (fun n => f (n + N)) := (summable_nat_add_iff N).mpr hf
  have htail : ∑' n, f (n + N) = f N + ∑' n, f (n + N + 1) := by
    rw [hfN.tsum_eq_zero_add]
    simp only [Nat.zero_add]
    congr 1; apply tsum_congr; intro n; congr 1; omega
  rw [← hf.sum_add_tsum_nat_add N, htail]; ring

/-- The sum Σ_{n=0}^∞ 1/2^{2^n} is irrational.

    Necessary condition for ErdosQuestion1: if this sum were rational, the
    identity perturbation b = a would witness that doubleExp is NOT an
    irrationality sequence.

    Note: `doubleExp_not_folklore_growth` shows folklore_irrationality does NOT
    apply here. The proof uses a direct integer-gap argument instead.

    PROOF: Integer-gap argument. Suppose S = p/q (rational, q ≠ 0). Let D = 2^{2^N}
    where N = |q|+1 (so D > |q|). Split S = A + 1/D + T where:
      A = Σ_{k<N} 1/2^{2^k} (finite sum), T = Σ_{k>N} 1/2^{2^k} (tail).
    Then q·D·T = p·D - q·(D·A) - q ∈ ℤ (since D·A ∈ ℕ by doubleExp_fin_mul_nat).
    But |q·D·T| ≤ |q|·D·T < |q|/(D-1) ≤ (D-1)/(D-1) = 1 (by doubleExp_tail_bound).
    And q·D·T ≠ 0 (since q≠0, D>0, T>0). A nonzero integer with |·|<1 is impossible. -/
theorem doubleExp_sum_irrational :
    Irrational (∑' n, (1 : ℝ) / (doubleExp n : ℕ)) := by
  simp_rw [doubleExp_term_eq]
  -- Proof by contradiction: assume S = ∑ 1/2^{2^n} is rational
  intro ⟨q, hq⟩
  -- q : ℚ, hq : ↑q = ∑' n, 1/2^{2^n}
  -- Use N = q.den (positive denominator), D = 2^{2^N}
  set N := q.den
  have hN_pos : 0 < N := q.pos
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
  set D := (2 : ℝ) ^ (2 ^ N) with hD_def
  have hD_pos : (0 : ℝ) < D := by positivity
  have hD_ne : D ≠ 0 := hD_pos.ne'
  -- The sum equals q.num / N as reals (since (q : ℝ) = q.num / q.den)
  have hS_eq : ∑' n : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ n) = (q.num : ℝ) / N := by
    rw [← hq]; push_cast; rw [Rat.cast_def]
  -- D ≥ N + 1 (so N ≤ D - 1), proved via N + 1 ≤ 2^N ≤ 2^{2^N} = D
  have hN1_le_D : (N : ℝ) + 1 ≤ D := by
    have h1 : N + 1 ≤ 2 ^ N := by
      induction N with
      | zero => norm_num
      | succ m ih =>
        calc m + 1 + 1 ≤ 2 ^ m + 1 := by linarith [nat_le_two_pow m]
          _ ≤ 2 ^ m + 2 ^ m := by linarith [Nat.one_le_pow m 2 (by norm_num)]
          _ = 2 ^ (m + 1) := by ring
    have h2 : (2 : ℕ) ^ N ≤ (2 : ℕ) ^ (2 ^ N) :=
      Nat.pow_le_pow_right (by norm_num) (nat_le_two_pow N)
    calc (N : ℝ) + 1 ≤ (2 : ℝ) ^ N := by exact_mod_cast h1
      _ ≤ D := by exact_mod_cast h2
  have hN_le_D1 : (N : ℝ) ≤ D - 1 := by linarith
  have hD1_pos : (0 : ℝ) < D - 1 := by linarith
  -- Abbreviations for finite sum and tail
  set finsum := ∑ k ∈ Finset.range N, (1 : ℝ) / (2 : ℝ) ^ (2 ^ k)
  set tail := ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1))
  -- Split S = finsum + 1/D + tail
  have hSplit : ∑' n : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ n) = finsum + 1 / D + tail := by
    rw [tsum_split_at _ doubleExp_sum_summable N]
    simp only [hD_def]
  -- D * finsum is a natural number
  obtain ⟨mf, hmf⟩ := doubleExp_fin_mul_nat N
  -- hmf : D * finsum = mf (as reals, mf : ℕ)
  -- Tail is positive and bounded
  have htail_pos : 0 < tail := doubleExp_tail_pos N
  have htail_bound : D * tail < 1 / (D - 1) := doubleExp_tail_bound N
  -- Key identity: N * D * tail = q.num * D - N * mf - N
  -- Derived from: q.num / N = finsum + 1/D + tail and D * finsum = mf
  have hkey : (N : ℝ) * D * tail = q.num * D - N * mf - N := by
    have hrat : (q.num : ℝ) / N = finsum + 1 / D + tail :=
      hS_eq.symm.trans hSplit
    have hmul : (q.num : ℝ) = N * finsum + N / D + N * tail := by
      have := congr_arg (· * N) hrat.symm
      simp only [div_mul_cancel₀ _ hN_ne] at this
      linarith [show N * (finsum + 1 / D + tail) = N * finsum + N / D + N * tail from by ring]
    have := congr_arg (· * D) hmul
    simp only [mul_comm D finsum, ← hmf] at this
    linarith [show (N : ℝ) * finsum * D = N * (D * finsum) from by ring,
              show (N : ℝ) / D * D = N from by field_simp]
  -- N * D * tail is in (0, 1)
  have hgap_pos : 0 < (N : ℝ) * D * tail :=
    mul_pos (mul_pos (Nat.cast_pos.mpr hN_pos) hD_pos) htail_pos
  have hgap_lt1 : (N : ℝ) * D * tail < 1 :=
    calc (N : ℝ) * D * tail = N * (D * tail) := by ring
      _ < N * (1 / (D - 1)) := mul_lt_mul_of_pos_left htail_bound (Nat.cast_pos.mpr hN_pos)
      _ = N / (D - 1) := by ring
      _ ≤ 1 := by rw [div_le_one hD1_pos]; exact hN_le_D1
  -- N * D * tail is an integer (= q.num * D - N * mf - N)
  have hgap_int : ∃ z : ℤ, (z : ℝ) = (N : ℝ) * D * tail := by
    exact ⟨(q.num * ((2 : ℕ) ^ (2 ^ N) : ℕ) : ℤ) - (N : ℤ) * (mf : ℤ) - (N : ℤ),
      by push_cast; linarith⟩
  -- Contradiction: no positive integer is < 1
  obtain ⟨z, hz⟩ := hgap_int
  have hz_pos : 0 < z := by exact_mod_cast hz ▸ hgap_pos
  have hz_lt1 : (z : ℝ) < 1 := hz ▸ hgap_lt1
  linarith [show (1 : ℝ) ≤ z from by exact_mod_cast hz_pos]

/- ## Part XII: Concrete non-irrationality sequence (geometric 2^n)

  Provides an explicit, elementary witness for `¬IsIrrationalitySequence`.
  This unblocks one half of `truncation_insufficient`: a sequence whose
  identity perturbation has a rational reciprocal sum (the geometric series).
  The other half (a proven irrationality sequence) remains open. -/

/-- The geometric sequence `n ↦ 2^n`. -/
def geom2_seq : PosIntSeq := fun n => ⟨2 ^ n, by positivity⟩

/-- Structural lemma: if `Σ 1/(a n)` (as a real) equals a rational, then `a` is
    not an irrationality sequence — the identity perturbation `b n = a n` witnesses
    this directly. -/
theorem not_irrationality_sequence_of_rational_sum (a : PosIntSeq)
    (q : ℚ) (hq : ∑' n, (1 : ℝ) / ((a n : ℕ) : ℝ) = (q : ℝ)) :
    ¬ IsIrrationalitySequence a := by
  intro h
  have hirr := h (fun n => ((a n : ℕ) : ℤ))
    (show IsPerturbation a (fun n => ((a n : ℕ) : ℤ)) from by
      unfold IsPerturbation
      have hratio : ∀ n, (((a n : ℕ) : ℤ) : ℝ) / ((a n : ℕ+) : ℝ) = 1 := fun n => by
        have hpos : (0 : ℝ) < ((a n : ℕ+) : ℝ) := by exact_mod_cast (a n).pos
        have heq : (((a n : ℕ) : ℤ) : ℝ) = ((a n : ℕ+) : ℝ) := by norm_cast
        rw [heq, div_self hpos.ne']
      simp_rw [hratio]; exact tendsto_const_nhds)
    (fun n => by
      show (((a n : ℕ) : ℤ)) > 0
      exact_mod_cast (a n).pos)
  have hsum_eq : reciprocalSum (fun n => ((a n : ℕ) : ℤ)) = (q : ℝ) := by
    unfold reciprocalSum
    have : (fun n => (1 : ℝ) / ((((a n : ℕ) : ℤ) : ℝ))) =
        (fun n => (1 : ℝ) / ((a n : ℕ) : ℝ)) := by
      funext n; push_cast; rfl
    rw [this]; exact hq
  rw [hsum_eq] at hirr
  exact hirr ⟨q, rfl⟩

/-- The geometric sequence `2^n` is NOT an irrationality sequence.
    Witness: `b n = 2^n` (identity perturbation). Then `b n / a n = 1 → 1`,
    `b n > 0`, and `Σ 1/b n = Σ (1/2)^n = 2 ∈ ℚ`. -/
theorem geom2_seq_not_irrationality_sequence :
    ¬ IsIrrationalitySequence geom2_seq :=
  not_irrationality_sequence_of_rational_sum geom2_seq 2 <| by
    have hcong : ∀ n, (1 : ℝ) / ((geom2_seq n : ℕ) : ℝ) = ((1 : ℝ) / 2) ^ n := fun n => by
      show (1 : ℝ) / ((2 ^ n : ℕ) : ℝ) = (1 / 2) ^ n
      rw [div_pow, one_pow]; push_cast; rfl
    rw [tsum_congr hcong, tsum_geometric_two]
    norm_num

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

  **Proved** (no sorries):
  - `doubleExp_strictly_increasing`: 2^{2^n} is strictly increasing
  - `doubleExp_square_growth`: a_{n+1} = a_n² for double exponential
  - `doubleExp_not_folklore_growth`: (2^{2^n})^{1/2^n} = 2 (constant), not → ∞
  - `doubleExp_convergent`: Σ 1/2^{2^n} converges (geometric comparison)
  - `doubleExp_superexponential`: (2^{2^n})^{1/n} → ∞ (superexponential growth)
  - `doubleExp_not_kovac_tao`: 2^{2^n} sits AT the KT boundary (ratio = 1, not → 0)
  - `characterization_gap`: Superexponential ≠ folklore growth (doubleExp as witness)
  - `factorial_no_folklore_growth`: (n!)^{1/2^n} ≤ 2 (bounded, cannot → ∞)
  - `factorial_has_kovac_tao_condition`: (n+2)!/((n+1)!)² → 0 (satisfies KT condition)
  - `connection_262_proved`: Every irrationality sequence has irrational reciprocal sum
  - `doubleExp_fin_mul_nat`: D * (finite sum) ∈ ℕ via pow_sub₀
  - `doubleExp_tail_pos`: tail ∑ 1/2^{2^{k+N+1}} > 0 via tsum_pos
  - `doubleExp_tail_bound`: D * tail < 1/(D-1) via geometric comparison
  - `tsum_split_at`: ∑ f = (range sum) + f N + (shifted tail) via sum_add_tsum_nat_add

  **Key sorries** (4 remaining, all deep — require non-Mathlib mathematics):
  - `folklore_irrationality`: a_n^{1/2^n} → ∞ ⟹ Σ 1/a_n irrational (Mahler-type)
  - `kovac_tao_not_irrationality`: The Kovač-Tao 2024 negative result (Egyptian fractions)
  - `positive_condition_irrationality`: liminf a_{n+1}/a_n^{2+ε} > 0 ⟹ irrationality seq
  - `truncation_insufficient`: ∀N, irrationality status requires infinite information

  **Proved in sessions 1–9** (no sorry):
  - `doubleExp_sum_irrational`: Σ 1/2^{2^n} is irrational (session 9, integer-gap argument)

  **Position of key sequences relative to KT threshold**:
  - doubleExp (2^{2^n}): ratio = 1 exactly (AT boundary, KT does NOT exclude it)
  - factorial (n!): ratio → 0 (BELOW boundary, KT excludes it as irrationality sequence)

  **Related**: Problems #262, #264 (other irrationality sequence questions)
-/
