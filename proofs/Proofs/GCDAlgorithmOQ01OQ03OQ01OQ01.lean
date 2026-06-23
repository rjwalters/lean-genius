/-
  Lamé's Theorem in Closed Form: the Euclidean step count is ≤ log_φ(b) + 1
  Open Question OQ-01 from GCDAlgorithmOQ01OQ03OQ01

  The grandparent entry (gcd-algorithm-oq-01-oq-03, "Binet's Formula and Lamé's
  5-Digit Bound") develops the golden ratio φ = (1+√5)/2, Binet's formula, and
  φ² = φ + 1.  The parent entry (gcd-algorithm-oq-01-oq-03-oq-01) proves Lamé
  sharpness — in particular the *minimality* bound

      0 < b < a  ∧  euclidSteps a b = n  →  fib (n+1) ≤ b.

  This file answers open question #1 of the parent: translate the exact
  worst-case count into the closed-form logarithmic bound

      euclidSteps a b = n  →  (n : ℝ) ≤ log_φ(b) + 1,

  i.e. the number of Euclidean steps on a pair with smaller entry `b` is at most
  one more than log base φ of `b`.  This is the quantitative content of Lamé's
  1844 analysis: the step count grows like log_φ(b), with the constant
  1/log₂(φ) ≈ 1.4404 when expressed in bits.

  Proof outline:
  1. φⁿ ≤ fib(n+2)            (two-step induction using φ² = φ + 1)
  2. fib(n+1) ≤ b             (parent's minimality bound)
  3. φ^(n-1) ≤ b              (combine 1 and 2)
  4. n - 1 ≤ log_φ(b)         (monotonicity of log_φ, log_φ(φ^(n-1)) = n-1)
  5. log₂(φ) > 2/3            (since φ³ = 2φ+1 > 4), making the Lamé constant
     1/log₂(φ) explicit and bounded above by 3/2.

  References:
  - Lamé, G. (1844). Note sur la limite du nombre des divisions...
  - GCDAlgorithmOQ01OQ03.lean      (Binet's formula, golden ratio φ).
  - GCDAlgorithmOQ01OQ03OQ01.lean  (Lamé sharpness, minimality bound).
-/
import Mathlib
import Proofs.GCDAlgorithmOQ01OQ03
import Proofs.GCDAlgorithmOQ01OQ03OQ01

namespace GCDAlgorithmOQ01OQ03OQ01OQ01

open Nat BinaryGcdOQ01 GCDAlgorithmOQ01OQ03.Binet GCDAlgorithmOQ01OQ03OQ01

-- ═══════════════════════════════════════════════════════════════════
-- PART I: ELEMENTARY GOLDEN-RATIO BOUNDS
-- ═══════════════════════════════════════════════════════════════════

/-- `φ > 3/2`, since `√5 > 2`. -/
theorem phi_gt_three_halves : (3 : ℝ) / 2 < goldenPhi := by
  unfold goldenPhi
  have := sqrt5_gt_two
  linarith

/-- `1 < φ`. -/
theorem one_lt_phi : (1 : ℝ) < goldenPhi := by
  have := phi_gt_three_halves; linarith

/-- `φ < 2`, since `√5 < 3`. -/
theorem phi_lt_two : goldenPhi < 2 := by
  have h : Real.sqrt 5 < 3 := by nlinarith [sqrt5_sq, sqrt5_pos]
  unfold goldenPhi; linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART II: GEOMETRIC LOWER BOUND  φⁿ ≤ fib(n+2)
-- ═══════════════════════════════════════════════════════════════════

/-- **Geometric lower bound on Fibonacci numbers.**  `φⁿ ≤ fib(n+2)` for all `n`.

    Proof by two-step induction: the base cases are `φ⁰ = 1 ≤ fib 2 = 1` and
    `φ¹ = φ ≤ fib 3 = 2`, and the step uses `φ^(n+2) = φ^(n+1) + φⁿ` (from
    `φ² = φ + 1`) together with `fib(n+4) = fib(n+3) + fib(n+2)`. -/
theorem phi_pow_le_fib : ∀ n : ℕ, goldenPhi ^ n ≤ (Nat.fib (n + 2) : ℝ) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    have h2 : Nat.fib (0 + 2) = 1 := by decide
    rw [pow_zero, h2]; norm_num
  | one =>
    have h3 : Nat.fib (1 + 2) = 2 := by decide
    rw [pow_one, h3]; push_cast; linarith [phi_lt_two]
  | more n h0 h1 =>
    -- h0 : φ^n ≤ fib(n+2),  h1 : φ^(n+1) ≤ fib(n+3),  goal : φ^(n+2) ≤ fib(n+4)
    have hrec : goldenPhi ^ (n + 2) = goldenPhi ^ (n + 1) + goldenPhi ^ n := by
      have h2 : goldenPhi ^ (n + 2) = goldenPhi ^ n * goldenPhi ^ 2 := by ring
      rw [h2, phi_sq]; ring
    have hfib : (Nat.fib (n + 2 + 2) : ℝ) = (Nat.fib (n + 3) : ℝ) + (Nat.fib (n + 2) : ℝ) := by
      have e : Nat.fib (n + 2 + 2) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
      rw [e]; push_cast; ring
    rw [hrec, hfib]
    exact add_le_add h1 h0

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE φ-POWER LOWER BOUND ON THE SMALLER ENTRY
-- ═══════════════════════════════════════════════════════════════════

/-- **Geometric lower bound from the step count.**  If the Euclidean run on
    `0 < b < a` takes `n ≥ 1` steps, then `φ^(n-1) ≤ b`.

    Combines the parent's minimality bound `fib(n+1) ≤ b` with `φⁿ ≤ fib(n+2)`. -/
theorem phi_pow_le_smaller (a b n : ℕ) (hb : 0 < b) (hba : b < a) (hn : 1 ≤ n)
    (hsteps : euclidSteps a b = n) : goldenPhi ^ (n - 1) ≤ (b : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hfib : Nat.fib (m + 2) ≤ b := (fib_le_of_euclidSteps a b (m + 1) hb hba hsteps).1
  have hcast : (Nat.fib (m + 2) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hfib
  calc goldenPhi ^ (m + 1 - 1) = goldenPhi ^ m := by rw [Nat.add_sub_cancel]
    _ ≤ (Nat.fib (m + 2) : ℝ) := phi_pow_le_fib m
    _ ≤ (b : ℝ) := hcast

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: THE CLOSED-FORM LOGARITHMIC BOUND (LAMÉ)
-- ═══════════════════════════════════════════════════════════════════

/-- **Lamé's closed-form bound.**  The number of Euclidean steps on a pair
    `0 < b < a` is at most `log_φ(b) + 1`:

        euclidSteps a b = n  →  (n : ℝ) ≤ log_φ(b) + 1.

    Proof: from `φ^(n-1) ≤ b` and monotonicity of `log_φ` (base `φ > 1`),
    `n - 1 = log_φ(φ^(n-1)) ≤ log_φ(b)`. -/
theorem euclidSteps_le_logb (a b n : ℕ) (hb : 0 < b) (hba : b < a) (hn : 1 ≤ n)
    (hsteps : euclidSteps a b = n) :
    (n : ℝ) ≤ Real.logb goldenPhi b + 1 := by
  have hphi1 : (1 : ℝ) < goldenPhi := one_lt_phi
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpow : goldenPhi ^ m ≤ (b : ℝ) := by
    have h := phi_pow_le_smaller a b (m + 1) hb hba hsteps (by omega)
    rwa [Nat.add_sub_cancel] at h
  have hphipos : (0 : ℝ) < goldenPhi ^ m := pow_pos (by linarith) m
  have hmono : Real.logb goldenPhi (goldenPhi ^ m) ≤ Real.logb goldenPhi b :=
    Real.logb_le_logb_of_le hphi1 hphipos hpow
  rw [Real.logb_pow, Real.logb_self_eq_one hphi1, mul_one] at hmono
  push_cast
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART V: MAKING THE LAMÉ CONSTANT EXPLICIT  (log₂ φ ≈ 0.694, 1/log₂φ ≈ 1.4404)
-- ═══════════════════════════════════════════════════════════════════

/-- `2·log 2 < 3·log φ`, equivalently `φ³ > 4` (since `φ³ = 2φ + 1 > 4`). -/
theorem two_log_two_lt_three_log_phi :
    2 * Real.log 2 < 3 * Real.log goldenPhi := by
  have h4 : (4 : ℝ) < goldenPhi ^ 3 := by
    rw [phi_pow3]; have := phi_gt_three_halves; linarith
  have hlog : Real.log 4 < Real.log (goldenPhi ^ 3) :=
    Real.log_lt_log (by norm_num) h4
  rw [Real.log_pow] at hlog
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [hlog4] at hlog
  push_cast at hlog
  linarith

/-- **The Lamé constant, explicit.**  `log₂(φ) > 2/3`, so the worst-case Euclidean
    step count grows like `log₂(b)/log₂(φ)` with `1/log₂(φ) ≈ 1.4404 < 3/2`. -/
theorem logb_two_phi_gt : (2 : ℝ) / 3 < Real.logb 2 goldenPhi := by
  unfold Real.logb
  rw [lt_div_iff (Real.log_pos (by norm_num))]
  have := two_log_two_lt_three_log_phi
  linarith

/-- **Lamé's bound in bits.**  The Euclidean step count is at most
    `(3/2)·log₂(b) + 1`.  This is the textbook "≈ 1.44 log₂ b" Lamé bound,
    with the explicit (slightly loose) constant 3/2 in place of the optimal
    `1/log₂(φ) ≈ 1.4404`. -/
theorem euclidSteps_le_log2 (a b n : ℕ) (hb : 0 < b) (hba : b < a) (hn : 1 ≤ n)
    (hsteps : euclidSteps a b = n) :
    (n : ℝ) ≤ (3 / 2) * Real.logb 2 b + 1 := by
  have hb1R : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlogb_nonneg : 0 ≤ Real.log b := Real.log_nonneg hb1R
  have hmain : (n : ℝ) ≤ Real.logb goldenPhi b + 1 :=
    euclidSteps_le_logb a b n hb hba hn hsteps
  have hlogphi : 0 < Real.log goldenPhi := Real.log_pos one_lt_phi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcmp := two_log_two_lt_three_log_phi
  have hsub : (0 : ℝ) ≤ 3 * Real.log goldenPhi - 2 * Real.log 2 := by linarith
  have hkey : Real.logb goldenPhi b ≤ (3 / 2) * Real.logb 2 b := by
    unfold Real.logb
    have hrhs : (3 / 2 : ℝ) * (Real.log b / Real.log 2)
        = (3 * Real.log b) / (2 * Real.log 2) := by field_simp; ring
    rw [hrhs, div_le_div_iff hlogphi (by positivity)]
    nlinarith [mul_nonneg hlogb_nonneg hsub]
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: SANITY CHECKS
-- ═══════════════════════════════════════════════════════════════════

-- φⁿ ≤ fib(n+2) at small indices (φ³ = 2φ+1 ≈ 4.236 ≤ fib 5 = 5).
example : goldenPhi ^ 3 ≤ (Nat.fib 5 : ℝ) := phi_pow_le_fib 3

-- The geometric bound powers the closed form: e.g. on the Fibonacci pair
-- (fib 7, fib 6) = (13, 8), which takes 5 steps, the bound reads 5 ≤ log_φ(8) + 1.
example : (5 : ℝ) ≤ Real.logb goldenPhi (Nat.fib 6) + 1 := by
  -- `euclidSteps (fib 7) (fib 6) = 5` is the `n = 5` instance of the parent's
  -- worst-case identity `euclidSteps (fib (n+2)) (fib (n+1)) = n` — no `native_decide`.
  have h : euclidSteps (Nat.fib 7) (Nat.fib 6) = 5 := euclidSteps_fib 5 (by norm_num)
  have hlt : Nat.fib 6 < Nat.fib 7 := by decide
  exact euclidSteps_le_logb (Nat.fib 7) (Nat.fib 6) 5 (by decide) hlt (by norm_num) h

end GCDAlgorithmOQ01OQ03OQ01OQ01
