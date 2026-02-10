import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-
# Average-Case Complexity of the Euclidean Algorithm

## Open Question
"What is the average-case complexity of the Euclidean algorithm?"

## What This Proves
We formalize **Lamé's theorem** (1844), which gives the tight worst-case bound,
prove the worst case is achieved by consecutive Fibonacci numbers, derive
logarithmic and classical "5 digits" bounds, and build finite average
computation infrastructure toward Dixon's theorem.

## Status
- [x] Step counting function and basic properties
- [x] Lamé's theorem (Fibonacci lower bound)
- [x] Worst-case optimality (consecutive Fibonacci numbers)
- [x] Logarithmic step bound
- [x] Classical 5-digit bound
- [x] Finite average computation definitions
- [ ] Full average-case analysis (Dixon's theorem — requires measure theory)
-/

namespace GCDAlgorithmOQ01

open Nat

/-
## Step Counting
-/

/-- Count division steps in the Euclidean algorithm. -/
def euclideanSteps (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else euclideanSteps b (a % b) + 1
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero ‹b ≠ 0›)

-- Verify step counts
example : euclideanSteps 48 18 = 3 := by native_decide
example : euclideanSteps 6 0 = 0 := by native_decide
example : euclideanSteps 2 1 = 1 := by native_decide
example : euclideanSteps 3 2 = 2 := by native_decide
example : euclideanSteps 5 3 = 3 := by native_decide
example : euclideanSteps 8 5 = 4 := by native_decide
example : euclideanSteps 13 8 = 5 := by native_decide
example : euclideanSteps 21 13 = 6 := by native_decide
example : euclideanSteps 34 21 = 7 := by native_decide
example : euclideanSteps 55 34 = 8 := by native_decide

/-
## Unfolding Lemmas
-/

@[simp]
theorem euclideanSteps_zero (a : ℕ) : euclideanSteps a 0 = 0 := by
  rw [euclideanSteps]; simp

theorem euclideanSteps_pos_eq (a b : ℕ) (hb : 0 < b) :
    euclideanSteps a b = euclideanSteps b (a % b) + 1 := by
  rw [euclideanSteps]; simp [Nat.pos_iff_ne_zero.mp hb]

theorem euclideanSteps_ge_one (a : ℕ) {b : ℕ} (hb : 0 < b) :
    1 ≤ euclideanSteps a b := by
  rw [euclideanSteps_pos_eq a b hb]; omega

/-
## Lamé's Theorem

If the Euclidean algorithm takes n steps on (a, b) with b > 0,
then b ≥ fib(n+1). Additionally, the remainder a%b ≥ fib(n) when n ≥ 2.
-/

/-- Core Lamé bound by strong induction on steps. -/
theorem lame_pair_bound (n : ℕ) :
    ∀ a b, euclideanSteps a b = n → 0 < b →
    fib (n + 1) ≤ b ∧ (2 ≤ n → fib n ≤ a % b) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro a b hsteps hb
  match n with
  | 0 =>
    rw [euclideanSteps_pos_eq a b hb] at hsteps; omega
  | 1 =>
    rw [euclideanSteps_pos_eq a b hb] at hsteps
    have hr : a % b = 0 := by
      by_contra h
      have hpos : 0 < a % b := Nat.pos_of_ne_zero h
      have := euclideanSteps_ge_one b hpos; omega
    constructor
    · -- fib 2 = 1 ≤ b
      show fib (1 + 1) ≤ b
      have : fib (1 + 1) = 1 := by native_decide
      omega
    · intro h; omega
  | n + 2 =>
    rw [euclideanSteps_pos_eq a b hb] at hsteps
    set r := a % b with hr_def
    have hr_lt : r < b := Nat.mod_lt a hb
    have hsteps' : euclideanSteps b r = n + 1 := by omega
    by_cases hr0 : r = 0
    · rw [hr0, euclideanSteps_zero] at hsteps'; omega
    · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
      have ⟨ib_r, ir⟩ := ih (n + 1) (by omega) b r hsteps' hr_pos
      constructor
      · -- Need: fib(n+3) ≤ b
        show fib (n + 2 + 1) ≤ b
        rw [show n + 2 + 1 = (n + 1) + 2 from by omega, fib_add_two]
        -- ib_r: fib(n+2) ≤ r
        -- Need to also get fib(n+1) ≤ b % r
        -- When n+1 ≥ 2 (i.e., n ≥ 1), ir gives fib(n+1) ≤ b % r
        -- When n = 0, n+1 = 1, fib(1) = 1, and b % r ≥ 0, but we need more
        -- Actually: b = (b/r)*r + b%r, and b/r ≥ 1 since b > r
        -- So b ≥ r + b%r ≥ fib(n+2) + b%r
        -- If n ≥ 1: b%r ≥ fib(n+1) by ir, so b ≥ fib(n+2) + fib(n+1)
        -- If n = 0: fib(n+2) + fib(n+1) = fib(2) + fib(1) = 1 + 1 = 2
        --   ib_r gives fib(1) ≤ r, so r ≥ 1; also r < b means b ≥ 2
        --   and fib(n+3) = fib(3) = 2 ≤ b. ✓
        have h_eq := Nat.div_add_mod b r
        have hq : 1 ≤ b / r := Nat.div_pos (by omega) hr_pos
        have hqr : r ≤ b / r * r := le_mul_of_one_le_left (Nat.zero_le r) hq
        match n with
        | 0 =>
          -- fib 3 = 2, need b ≥ 2
          -- ib_r: fib 2 ≤ r, so r ≥ 1; r < b so b ≥ 2
          change fib 3 ≤ b
          have h3 : fib 3 = 2 := by native_decide
          have h2 : fib 2 = 1 := by native_decide
          have : fib 2 ≤ r := ib_r
          omega
        | n + 1 =>
          have ir' := ir (by omega)
          -- ib_r: fib(n+3) ≤ r, ir': fib(n+2) ≤ b % r
          -- b = (b/r)*r + b%r ≥ r + b%r ≥ fib(n+3) + fib(n+2)
          linarith
      · intro _
        -- Need fib(n+2) ≤ a % b = r
        exact ib_r

/-- **Lamé's Theorem**: fib(steps + 1) ≤ b when b > 0. -/
theorem lame_theorem (a b : ℕ) (hb : 0 < b) :
    fib (euclideanSteps a b + 1) ≤ b :=
  (lame_pair_bound (euclideanSteps a b) a b rfl hb).1

/-- **Lamé's Theorem (contrapositive)**: b < fib(k+2) implies steps ≤ k. -/
theorem lame_step_bound (a b : ℕ) (hb : 0 < b) (k : ℕ) (hk : b < fib (k + 2)) :
    euclideanSteps a b ≤ k := by
  by_contra h; push_neg at h
  have h1 := lame_theorem a b hb
  have h2 : fib (k + 2) ≤ fib (euclideanSteps a b + 1) := Nat.fib_mono (by omega)
  omega

/-
## Worst Case: Consecutive Fibonacci Numbers
-/

/-- F(n+2) mod F(n+1) = F(n) for n ≥ 2. -/
theorem fib_mod_fib (n : ℕ) (hn : 2 ≤ n) :
    fib (n + 2) % fib (n + 1) = fib n := by
  have h1 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
  have h2 : fib n < fib (n + 1) := fib_lt_fib_succ hn
  rw [h1, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt h2

/-- Consecutive Fibonacci numbers achieve the worst case:
    euclideanSteps(fib(n+2), fib(n+1)) = n for n ≥ 1. -/
theorem euclideanSteps_fib : ∀ n : ℕ, 1 ≤ n →
    euclideanSteps (fib (n + 2)) (fib (n + 1)) = n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    show euclideanSteps (fib (k + 3)) (fib (k + 2)) = k + 1
    cases k with
    | zero =>
      -- euclideanSteps (fib 3) (fib 2) = 1 — verify computationally
      native_decide
    | succ k =>
      have hfk2_pos : 0 < fib (k + 2 + 1) := Nat.fib_pos.mpr (by omega)
      have hmod : fib (k + 2 + 2) % fib (k + 2 + 1) = fib (k + 2) := by
        exact fib_mod_fib (k + 2) (by omega)
      rw [show k + 1 + 3 = k + 2 + 2 from by omega,
          show k + 1 + 2 = k + 2 + 1 from by omega]
      rw [euclideanSteps_pos_eq _ _ hfk2_pos, hmod]
      have := ih (by omega)
      rw [show k + 1 + 2 = k + 3 from by omega, show k + 1 + 1 = k + 2 from by omega] at this
      rw [show k + 2 + 1 = k + 3 from by omega]
      omega

-- Verify worst-case saturation
example : fib (euclideanSteps 89 55 + 1) = 55 := by native_decide
example : fib (euclideanSteps 55 34 + 1) = 34 := by native_decide

/-
## Logarithmic Bound
-/

/-- fib(2n+1) ≥ 2^n for all n. -/
theorem fib_exponential_lower : ∀ n : ℕ, 2 ^ n ≤ fib (2 * n + 1) := by
  intro n
  induction n with
  | zero => simp [fib_one]
  | succ k ih =>
    -- fib(2(k+1)+1) = fib(2k+3) = fib((2k+1)+2) = fib(2k+2) + fib(2k+1)
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega, fib_add_two]
    -- fib(2k+2) = fib((2k)+2) = fib(2k) + fib(2k+1)
    have h_fib_succ : fib ((2 * k + 1) + 1) = fib (2 * k) + fib (2 * k + 1) := by
      rw [show (2 * k + 1) + 1 = (2 * k) + 2 from by omega, fib_add_two]
    rw [h_fib_succ]
    -- Now goal: 2^(k+1) ≤ fib(2k+1) + (fib(2k) + fib(2k+1))
    -- = 2*fib(2k+1) + fib(2k)
    -- ≥ 2*fib(2k+1) ≥ 2*2^k = 2^(k+1)
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

/-- steps ≤ 2 * log₂(b) + 2. -/
theorem euclideanSteps_log_bound (a b : ℕ) (hb : 0 < b) :
    euclideanSteps a b ≤ 2 * Nat.log 2 b + 2 := by
  apply lame_step_bound a b hb (2 * Nat.log 2 b + 2)
  set L := Nat.log 2 b
  have hb_lt : b < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < 2) b
  have hfib_ge : 2 ^ (L + 1) ≤ fib (2 * (L + 1) + 1) := fib_exponential_lower (L + 1)
  have hfib_mono : fib (2 * (L + 1) + 1) ≤ fib (2 * L + 4) := Nat.fib_mono (by omega)
  calc b < 2 ^ (L + 1) := hb_lt
    _ ≤ fib (2 * (L + 1) + 1) := hfib_ge
    _ ≤ fib (2 * L + 4) := hfib_mono

/-
## Lamé's Classical "5-Digit" Bound
-/

/-- Number of decimal digits: ⌊log₁₀(b)⌋ + 1. -/
def decimalDigits (b : ℕ) : ℕ := Nat.log 10 b + 1

example : decimalDigits 1 = 1 := by native_decide
example : decimalDigits 9 = 1 := by native_decide
example : decimalDigits 10 = 2 := by native_decide
example : decimalDigits 99 = 2 := by native_decide
example : decimalDigits 100 = 3 := by native_decide

/-- fib(5k + 2) ≥ 10^k for k ≤ 20. -/
theorem fib_ge_pow10 : ∀ k : ℕ, k ≤ 20 → 10 ^ k ≤ fib (5 * k + 2) := by
  intro k hk; interval_cases k <;> native_decide

/-- **Lamé's 5-Digit Bound**: steps ≤ 5 × decimalDigits(b) for b < 10^20. -/
theorem lame_five_digit_bound (a b : ℕ) (hb : 0 < b) (hb_bound : b < 10 ^ 20) :
    euclideanSteps a b ≤ 5 * decimalDigits b := by
  unfold decimalDigits
  set d := Nat.log 10 b
  apply lame_step_bound a b hb
  have hb_lt : b < 10 ^ (d + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < 10) b
  have hd_bound : d + 1 ≤ 20 := by
    by_contra h; push_neg at h
    have h1 : 10 ^ 20 ≤ 10 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 10 ^ d ≤ b := Nat.pow_log_le_self 10 (by omega : b ≠ 0)
    omega
  have hfib : 10 ^ (d + 1) ≤ fib (5 * (d + 1) + 2) := fib_ge_pow10 (d + 1) hd_bound
  omega

-- Verify
example : euclideanSteps 48 18 ≤ 5 * decimalDigits 18 := by native_decide
example : euclideanSteps 1000 373 ≤ 5 * decimalDigits 373 := by native_decide

/-
## Finite Average Computation

Infrastructure for computing exact averages over bounded inputs,
providing numerical evidence for Dixon's asymptotic formula.
-/

/-- Total Euclidean steps over all pairs (a, b) with a ∈ [1,N], b ∈ [1,a]. -/
def totalSteps (N : ℕ) : ℕ :=
  (Finset.range N).sum fun i =>
    (Finset.range (i + 1)).sum fun j =>
      euclideanSteps (i + 1) (j + 1)

/-- Count of pairs. -/
def pairCount (N : ℕ) : ℕ := N * (N + 1) / 2

example : pairCount 1 = 1 := by native_decide
example : pairCount 10 = 55 := by native_decide

-- Verify small totalSteps values
example : totalSteps 1 = 1 := by native_decide
example : totalSteps 2 = 3 := by native_decide
example : totalSteps 3 = 7 := by native_decide

/-
## Summary

### Proved Results
1. **euclideanSteps** — step counting function
2. **lame_pair_bound** — core inductive Lamé proof
3. **lame_theorem** — fib(steps+1) ≤ b
4. **lame_step_bound** — contrapositive: b < fib(k+2) → steps ≤ k
5. **euclideanSteps_fib** — worst case: consecutive Fibonacci numbers
6. **fib_exponential_lower** — fib(2n+1) ≥ 2^n
7. **euclideanSteps_log_bound** — steps ≤ 2·log₂(b) + 2
8. **lame_five_digit_bound** — steps ≤ 5·digits(b) for b < 10²⁰
9. **totalSteps/pairCount** — finite average infrastructure

### Dixon's Theorem (not formalized)
The average number of steps is (12 ln 2 / π²) ln N ≈ 0.8427 ln N.
This requires continued fractions, the Gauss map, and ergodic theory
(not available in Mathlib v4.26.0).
-/

end GCDAlgorithmOQ01
