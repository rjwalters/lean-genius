/-
# Collatz Conjecture for Structured Starting Values

This file proves that the Collatz sequence reaches 1 for specific
structured starting values, particularly powers of 2.

**Status**: DEEP DIVE
- Defines the Collatz function
- Proves powers of 2 reach 1
- Proves closure properties
- Verifies small computed values

**The Collatz Conjecture**:
For any positive integer n, repeatedly applying:
- n → n/2 if n is even
- n → 3n+1 if n is odd
eventually reaches 1.

This conjecture is UNSOLVED for general n, but we prove it for:
- Powers of 2: 2^k (trivial)
- Numbers of form 2^k * m where m reaches 1
-/

import Mathlib.Tactic

namespace Collatz

/-!
## The Collatz Function
-/

/-- The Collatz function: n → n/2 if even, n → 3n+1 if odd -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Collatz of 0 is 0 -/
@[simp] theorem collatz_zero : collatz 0 = 0 := by simp [collatz]

/-- Collatz of 1 is 4 -/
@[simp] theorem collatz_one : collatz 1 = 4 := by simp [collatz]

/-- Collatz of an even number is halving -/
theorem collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

/-- Collatz of an odd number is 3n+1 -/
theorem collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, h]

/-- Collatz of 2n is n -/
theorem collatz_two_mul (n : ℕ) : collatz (2 * n) = n := by
  simp [collatz, Nat.mul_mod_right]

/-- Alternative: collatz(2n) = n -/
theorem collatz_double (n : ℕ) : collatz (2 * n) = n := collatz_two_mul n

/-!
## Reaching 1

We define what it means for a number to "reach 1" under Collatz iteration.
-/

/-- Iterate the Collatz function k times -/
def collatzIter (k : ℕ) (n : ℕ) : ℕ := collatz^[k] n

/-- A number reaches 1 if some iterate equals 1 -/
def ReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, collatzIter k n = 1

/-- 1 reaches 1 (in 0 steps) -/
theorem one_reaches_one : ReachesOne 1 := ⟨0, rfl⟩

/-- The number of steps to reach 1, if it exists -/
noncomputable def stepsToOne (n : ℕ) (h : ReachesOne n) : ℕ :=
  Nat.find h

/-!
## Powers of 2 Reach 1

The key theorem: 2^k reaches 1 in exactly k steps (for k ≥ 1).
-/

/-- 2 reaches 1 (in 1 step: 2 → 1) -/
theorem two_reaches_one : ReachesOne 2 := by
  use 1
  simp [collatzIter, collatz]

/-- collatzIter k (2^k) = 1 for k ≥ 1 -/
theorem collatz_pow_two (k : ℕ) (hk : k ≥ 1) : collatzIter k (2^k) = 1 := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- k = 1: 2^1 = 2 → 1
      simp [collatzIter, collatz]
    | succ m =>
      -- k = m + 2: 2^(m+2) → 2^(m+1) → ... → 1
      simp only [collatzIter]
      have h2 : 2^(m + 2) = 2 * 2^(m + 1) := by ring
      conv_lhs => rw [h2]
      rw [Function.iterate_succ_apply]
      simp only [collatz_two_mul]
      have : collatz^[m + 1] (2 ^ (m + 1)) = 1 := ih (by omega)
      exact this

/-- 2^k reaches 1 for all k ≥ 1 -/
theorem pow_two_reaches_one (k : ℕ) (hk : k ≥ 1) : ReachesOne (2^k) :=
  ⟨k, collatz_pow_two k hk⟩

/-!
## Closure Properties

If n reaches 1, then 2n, 4n, 8n, ... also reach 1.
-/

/-- If n reaches 1 in k steps, then 2n reaches 1 in k+1 steps -/
theorem reaches_one_double {n : ℕ} (h : ReachesOne n) : ReachesOne (2 * n) := by
  obtain ⟨k, hk⟩ := h
  use k + 1
  simp only [collatzIter] at hk ⊢
  rw [Function.iterate_succ_apply, collatz_two_mul]
  exact hk

/-- If n reaches 1, then 2^m * n reaches 1 -/
theorem reaches_one_pow_two_mul {n : ℕ} (m : ℕ) (h : ReachesOne n) :
    ReachesOne (2^m * n) := by
  induction m with
  | zero => simpa
  | succ k ih =>
    have h2 : 2^(k+1) * n = 2 * (2^k * n) := by ring
    rw [h2]
    exact reaches_one_double ih

/-!
## Computed Small Values

Verify specific small values reach 1.
-/

-- Compute: collatz(3) = 10
example : collatz 3 = 10 := by native_decide

-- Compute: collatz(10) = 5
example : collatz 10 = 5 := by native_decide

-- Compute: collatz(5) = 16
example : collatz 5 = 16 := by native_decide

-- Compute: collatz(16) = 8
example : collatz 16 = 8 := by native_decide

/-- 3 reaches 1: 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 (7 steps) -/
theorem three_reaches_one : ReachesOne 3 := by
  use 7
  native_decide

/-- 5 reaches 1 -/
theorem five_reaches_one : ReachesOne 5 := by
  use 5
  native_decide

/-- 6 reaches 1 -/
theorem six_reaches_one : ReachesOne 6 := by
  use 8
  native_decide

/-- 7 reaches 1 -/
theorem seven_reaches_one : ReachesOne 7 := by
  use 16
  native_decide

/-- 9 reaches 1 -/
theorem nine_reaches_one : ReachesOne 9 := by
  use 19
  native_decide

/-- 27 reaches 1 (famous for taking 111 steps) -/
theorem twentyseven_reaches_one : ReachesOne 27 := by
  use 111
  native_decide

/-!
## The Collatz Conjecture (Statement)

We state the full conjecture as an axiom, since it's unsolved.
-/

/-- The Collatz Conjecture: every positive integer reaches 1 -/
axiom collatz_conjecture : ∀ n : ℕ, n ≥ 1 → ReachesOne n

/-!
## Summary

**What We Proved**:
1. ✓ Powers of 2 reach 1: 2^k → 2^(k-1) → ... → 1
2. ✓ Closure: if n reaches 1, so does 2n, 4n, etc.
3. ✓ Specific values: 3, 5, 6, 7, 9, 27 verified
4. ✓ 27 takes 111 steps (famous example)

**What Remains Open**:
- The full Collatz conjecture (all n ≥ 1)
- Proving 2^n - 1 reaches 1 (harder pattern)
- Upper bounds on stopping time
-/

end Collatz
