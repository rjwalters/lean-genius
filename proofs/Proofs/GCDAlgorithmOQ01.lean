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
- [x] GCD preservation and structural properties
- [x] Tight Lamé remainder bound characterization
- [x] Translation invariance: steps(a + kb, b) = steps(a, b)
- [x] Swap lemma: a < b implies steps(a,b) = steps(b,a) + 1
- [x] Finite average computation definitions
- [x] Crude bounds: steps ≤ b, steps(a,1) = 1, steps(a,a) = 1
- [x] GCD step invariant and termination characterization
- [x] Tight Lamé optimality: fib(n+1) is minimal b achieving n steps
- [x] Coprime step lower bound: coprime with b > 1 → steps ≥ 2
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
    · show fib (1 + 1) ≤ b
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
      · show fib (n + 2 + 1) ≤ b
        rw [show n + 2 + 1 = (n + 1) + 2 from by omega, fib_add_two]
        have h_eq := Nat.div_add_mod b r
        have hq : 1 ≤ b / r := Nat.div_pos (by omega) hr_pos
        have hqr : r ≤ b / r * r := le_mul_of_one_le_left (Nat.zero_le r) hq
        match n with
        | 0 =>
          change fib 3 ≤ b
          have h3 : fib 3 = 2 := by native_decide
          have h2 : fib 2 = 1 := by native_decide
          have : fib 2 ≤ r := ib_r
          omega
        | n + 1 =>
          have ir' := ir (by omega)
          linarith
      · intro _
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
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega, fib_add_two]
    have h_fib_succ : fib ((2 * k + 1) + 1) = fib (2 * k) + fib (2 * k + 1) := by
      rw [show (2 * k + 1) + 1 = (2 * k) + 2 from by omega, fib_add_two]
    rw [h_fib_succ]
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
## GCD Preservation
-/

/-- The Euclidean algorithm computes gcd: steps = 0 ↔ b = 0. -/
theorem euclideanSteps_eq_zero_iff (a b : ℕ) :
    euclideanSteps a b = 0 ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    have : 0 < b := Nat.pos_of_ne_zero hb
    have := euclideanSteps_ge_one a this
    omega
  · intro h; rw [h, euclideanSteps_zero]

/-- When b divides a, the algorithm takes exactly 1 step (if b > 0). -/
theorem euclideanSteps_dvd (a b : ℕ) (hb : 0 < b) (hdvd : b ∣ a) :
    euclideanSteps a b = 1 := by
  rw [euclideanSteps_pos_eq a b hb]
  have : a % b = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rw [this, euclideanSteps_zero]

/-- Step count for (b, 0) is 0. -/
@[simp]
theorem euclideanSteps_right_zero (b : ℕ) : euclideanSteps b 0 = 0 :=
  euclideanSteps_zero b

/-
## Tight Lamé Bound (Equality Characterization)
-/

/-- If steps = 1, then a % b = 0 (the algorithm terminates in one step). -/
theorem steps_one_remainder_zero (a b : ℕ) (hb : 0 < b)
    (hs : euclideanSteps a b = 1) : a % b = 0 := by
  rw [euclideanSteps_pos_eq a b hb] at hs
  have h0 : euclideanSteps b (a % b) = 0 := by omega
  rwa [euclideanSteps_eq_zero_iff] at h0

/-- If steps ≥ 2, then the remainder a%b ≥ fib(n). -/
theorem lame_remainder_bound (a b n : ℕ) (hb : 0 < b)
    (hs : euclideanSteps a b = n) (hn : 2 ≤ n) :
    fib n ≤ a % b :=
  (lame_pair_bound n a b hs hb).2 hn

/-
## Monotonicity and Structural Properties
-/

/-- Adding a multiple of b to a doesn't change the step count. -/
theorem euclideanSteps_add_mul (a b k : ℕ) (hb : 0 < b) :
    euclideanSteps (a + k * b) b = euclideanSteps a b := by
  rw [euclideanSteps_pos_eq (a + k * b) b hb]
  rw [Nat.add_mul_mod_self_right]
  by_cases hab : a % b = 0
  · rw [hab, euclideanSteps_zero]
    by_cases hab2 : b = 0
    · omega
    · rw [euclideanSteps_pos_eq a b hb, hab, euclideanSteps_zero]
  · rw [euclideanSteps_pos_eq a b hb]

/-- Euclidean steps when a < b: swapping adds one step. -/
theorem euclideanSteps_swap (a b : ℕ) (_ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    euclideanSteps a b = euclideanSteps b a + 1 := by
  rw [euclideanSteps_pos_eq a b hb, Nat.mod_eq_of_lt hab]

/-
## Finite Average Computation
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
## Step Reduction and Crude Bounds
-/

/-- The Euclidean algorithm makes progress: the step count decreases after one reduction. -/
theorem euclideanSteps_reduction (a b : ℕ) (hb : 0 < b) :
    euclideanSteps b (a % b) = euclideanSteps a b - 1 := by
  rw [euclideanSteps_pos_eq a b hb]; omega

/-- Steps ≤ b: a crude but useful upper bound. -/
theorem euclideanSteps_le_second (a b : ℕ) : euclideanSteps a b ≤ b := by
  induction a, b using euclideanSteps.induct with
  | case1 a => simp
  | case2 a b hb ih =>
    rw [euclideanSteps_pos_eq a b (Nat.pos_of_ne_zero hb)]
    have hmod_lt : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
    omega

/-- gcd(a, 1) always takes exactly 1 step. -/
theorem euclideanSteps_one (a : ℕ) : euclideanSteps a 1 = 1 := by
  rw [euclideanSteps_pos_eq a 1 (by omega)]
  simp [Nat.mod_one]

/-- Steps for (a, a) when a > 0 is always 1. -/
theorem euclideanSteps_self (a : ℕ) (ha : 0 < a) : euclideanSteps a a = 1 := by
  rw [euclideanSteps_pos_eq a a ha, Nat.mod_self, euclideanSteps_zero]

/-
## GCD Preserved Through Steps
-/

/-- The GCD is preserved through one step of the Euclidean algorithm:
    gcd(b, a mod b) = gcd(a, b). -/
theorem gcd_step_invariant (a b : ℕ) (_hb : 0 < b) :
    Nat.gcd b (a % b) = Nat.gcd a b := by
  have : Nat.gcd a b = Nat.gcd b a := Nat.gcd_comm a b
  have : Nat.gcd b a = Nat.gcd (a % b) b := Nat.gcd_rec b a
  have : Nat.gcd (a % b) b = Nat.gcd b (a % b) := Nat.gcd_comm (a % b) b
  linarith

/-- When the remainder is zero, the GCD equals b. -/
theorem gcd_eq_of_mod_zero (a b : ℕ) (_hb : 0 < b) (hab : a % b = 0) :
    Nat.gcd a b = b := by
  calc Nat.gcd a b = Nat.gcd b a := Nat.gcd_comm a b
    _ = Nat.gcd (a % b) b := Nat.gcd_rec b a
    _ = Nat.gcd 0 b := by rw [hab]
    _ = b := Nat.gcd_zero_left b

/-
## Lamé Lower Bound (Optimality)
-/

/-- For any n ≥ 1, there exists a pair achieving exactly n steps. -/
theorem exists_pair_with_steps (n : ℕ) (hn : 1 ≤ n) :
    ∃ a b, 0 < b ∧ euclideanSteps a b = n := by
  exact ⟨fib (n + 2), fib (n + 1), Nat.fib_pos.mpr (by omega),
         euclideanSteps_fib n hn⟩

/-- The minimal b achieving n steps is exactly fib(n+1). -/
theorem lame_tight (n : ℕ) (hn : 1 ≤ n) :
    (∀ a b, 0 < b → euclideanSteps a b = n → fib (n + 1) ≤ b) ∧
    (∃ a b, 0 < b ∧ euclideanSteps a b = n ∧ b = fib (n + 1)) := by
  constructor
  · intro a b hb hs
    exact (lame_pair_bound n a b hs hb).1
  · exact ⟨fib (n + 2), fib (n + 1), Nat.fib_pos.mpr (by omega),
           euclideanSteps_fib n hn, rfl⟩

/-
## Coprime Pairs and Step Counts
-/

/-- For coprime inputs with b > 1, the algorithm uses at least 2 steps. -/
theorem coprime_steps_ge_two (a b : ℕ) (hb : 1 < b) (hcop : Nat.Coprime a b) :
    2 ≤ euclideanSteps a b := by
  rw [euclideanSteps_pos_eq a b (by omega)]
  have hr : a % b ≠ 0 := by
    intro h
    have : b ∣ a := Nat.dvd_of_mod_eq_zero h
    have : b ∣ Nat.gcd a b := Nat.dvd_gcd this (dvd_refl b)
    rw [hcop] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hpos : 0 < a % b := Nat.pos_of_ne_zero hr
  have := euclideanSteps_ge_one b hpos
  omega

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
10. **euclideanSteps_eq_zero_iff** — steps = 0 ↔ b = 0
11. **euclideanSteps_dvd** — b ∣ a → steps = 1
12. **steps_one_remainder_zero** — steps = 1 → a%b = 0
13. **lame_remainder_bound** — steps ≥ 2 → fib(n) ≤ a%b
14. **euclideanSteps_add_mul** — steps(a + kb, b) = steps(a, b)
15. **euclideanSteps_swap** — a < b → steps(a,b) = steps(b,a) + 1
16. **euclideanSteps_reduction** — steps decrease by 1 each reduction
17. **euclideanSteps_le_second** — steps ≤ b (crude bound)
18. **euclideanSteps_one** — steps(a, 1) = 1
19. **euclideanSteps_self** — steps(a, a) = 1
20. **gcd_step_invariant** — gcd preserved through steps
21. **gcd_eq_of_mod_zero** — a%b = 0 → gcd(a,b) = b
22. **exists_pair_with_steps** — ∀ n ≥ 1, ∃ pair with exactly n steps
23. **lame_tight** — fib(n+1) is the minimal b achieving n steps
24. **coprime_steps_ge_two** — coprime with b > 1 → steps ≥ 2

### Dixon's Theorem (not formalized)
The average number of steps is (12 ln 2 / π²) ln N ≈ 0.8427 ln N.
This requires continued fractions, the Gauss map, and ergodic theory
(not available in Mathlib v4.26.0).
-/

end GCDAlgorithmOQ01
