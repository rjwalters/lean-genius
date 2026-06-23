/-
  Lehmer GCD OQ-01: Progress and Correctness of the Lehmer Step

  Formalizes the key correctness properties of the Lehmer/Euclidean GCD step:

  1. **Progress** (`lehmerGcd_progress`): One Lehmer step (b, a mod b) strictly
     decreases the sum a + b when 0 < b ≤ a.

  2. **Correctness** (`lehmerGcd_correct`): The iterated Lehmer algorithm
     computes the same GCD as Nat.gcd.

  The "Lehmer step" here is the Euclidean step (a, b) ↦ (b, a mod b), which is
  the inner step of Lehmer's 1938 algorithm. The classical Lehmer optimization
  performs multiple such steps using single-precision arithmetic; correctness
  of each step is the mathematical core.

  ## Key Results (0 sorries, 0 axioms)

  - `lehmerStep_gcd_invariant`: gcd(b, a mod b) = gcd(a, b)
  - `lehmerGcd_progress`: b + (a mod b) < a + b when 0 < b ≤ a
  - `lehmerGcd_correct`: lehmerGcd a b = Nat.gcd a b

  ## References
  - Lehmer, D.H. (1938). "Euclid's Algorithm for Large Numbers." Amer. Math. Monthly
  - Knuth, TAOCP Vol. 2, §4.5.2
  - Parent: BinaryGcdOQ03.lean (Lehmer-Schönhage hybrid, GCD invariance theory)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace LehmerGcdOQ01

-- ══════════════════════════════════════════════════════════════
-- § 1. The Lehmer Step: One Euclidean Division
-- ══════════════════════════════════════════════════════════════

/-- The Lehmer step: apply one Euclidean division to reduce (a, b).
    Maps (a, b) to (b, a mod b), which strictly decreases a + b when 0 < b ≤ a. -/
def lehmerStep (a b : ℕ) : ℕ × ℕ := (b, a % b)

-- ══════════════════════════════════════════════════════════════
-- § 2. GCD Invariance of the Lehmer Step
-- ══════════════════════════════════════════════════════════════

/-- The Lehmer step preserves GCD: gcd(lehmerStep a b) = gcd(a, b).
    This is the fundamental invariant that makes the algorithm correct.

    Note: Mathlib's `Nat.gcd_rec m n : Nat.gcd m n = Nat.gcd (n % m) m`,
    so we rewrite via commutativity to get the desired direction. -/
theorem lehmerStep_gcd_invariant (a b : ℕ) :
    Nat.gcd (lehmerStep a b).1 (lehmerStep a b).2 = Nat.gcd a b := by
  simp only [lehmerStep]
  -- Goal: Nat.gcd b (a % b) = Nat.gcd a b
  rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

/-- Equivalent formulation: gcd(b, a mod b) = gcd(a, b). -/
theorem lehmerStep_gcd (a b : ℕ) : Nat.gcd b (a % b) = Nat.gcd a b := by
  rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

-- ══════════════════════════════════════════════════════════════
-- § 3. Progress: The Lehmer Step Strictly Decreases a + b
-- ══════════════════════════════════════════════════════════════

/-- **Main Progress Theorem**: One Lehmer step strictly decreases a + b.
    Requires 0 < b ≤ a (the algorithm maintains this invariant).

    Proof: Since 0 < b ≤ a, we have a mod b < b ≤ a.
    Therefore (lehmerStep a b).1 + (lehmerStep a b).2
           = b + (a mod b) < a + b. -/
theorem lehmerGcd_progress (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    (lehmerStep a b).1 + (lehmerStep a b).2 < a + b := by
  simp only [lehmerStep]
  -- Need: b + a % b < a + b, i.e., a % b < a
  have hmod : a % b < b := Nat.mod_lt a hb
  omega

/-- Alternative: without the normalization hypothesis, the sum is bounded by max. -/
theorem lehmerGcd_progress' (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    let (a', b') := if a ≥ b then lehmerStep a b else lehmerStep b a
    a' + b' < a + b := by
  simp only
  split_ifs with h
  · -- a ≥ b > 0
    simp [lehmerStep]
    have hmod : a % b < b := Nat.mod_lt a hb
    omega
  · -- b > a > 0
    simp [lehmerStep]
    push_neg at h
    have hmod : b % a < a := Nat.mod_lt b ha
    omega

-- ══════════════════════════════════════════════════════════════
-- § 4. The Lehmer GCD Algorithm
-- ══════════════════════════════════════════════════════════════

/-- The Lehmer GCD algorithm: repeatedly apply Euclidean (Lehmer) steps,
    always working with the larger of the two inputs first.

    This is a clean formalization of Lehmer's core algorithm. Termination is
    witnessed by the strictly decreasing measure a + b (see progress theorem). -/
def lehmerGcd : ℕ → ℕ → ℕ
  | 0, b => b
  | a, 0 => a
  | a + 1, b + 1 =>
    if a + 1 ≥ b + 1 then
      -- Apply Lehmer step: (a+1, b+1) ↦ (b+1, (a+1) % (b+1))
      lehmerGcd (b + 1) ((a + 1) % (b + 1))
    else
      -- Swap and apply: (b+1, a+1) ↦ (a+1, (b+1) % (a+1))
      lehmerGcd (a + 1) ((b + 1) % (a + 1))
termination_by a b => a + b
decreasing_by
  · -- Case a + 1 ≥ b + 1: measure decreases from (a+1)+(b+1) to (b+1) + ((a+1)%(b+1))
    rename_i h
    have hmod : (a + 1) % (b + 1) < b + 1 := Nat.mod_lt _ (Nat.succ_pos b)
    omega
  · -- Case a + 1 < b + 1: measure decreases from (a+1)+(b+1) to (a+1) + ((b+1)%(a+1))
    rename_i h
    push_neg at h
    have hmod : (b + 1) % (a + 1) < a + 1 := Nat.mod_lt _ (Nat.succ_pos a)
    omega

-- ══════════════════════════════════════════════════════════════
-- § 5. Correctness: lehmerGcd = Nat.gcd
-- ══════════════════════════════════════════════════════════════

/-- **Correctness Theorem**: The Lehmer GCD algorithm computes the true GCD.

    Proof by well-founded induction on a + b:
    - Base cases (a=0, b=0): Nat.gcd 0 b = b and Nat.gcd a 0 = a by definition.
    - Recursive case: The Lehmer step (a, b) ↦ (b, a mod b) preserves GCD
      by `Nat.gcd_rec`, and similarly for the swapped case. -/
theorem lehmerGcd_correct (a b : ℕ) : lehmerGcd a b = Nat.gcd a b := by
  induction a, b using lehmerGcd.induct with
  | case1 b =>
    -- a = 0: lehmerGcd 0 b = b = Nat.gcd 0 b
    simp [lehmerGcd]
  | case2 a =>
    -- b = 0: lehmerGcd (a+1) 0 = a+1 = Nat.gcd (a+1) 0
    simp [lehmerGcd]
  | case3 a b hge ih =>
    -- a+1 ≥ b+1: lehmerGcd (a+1) (b+1) = lehmerGcd (b+1) ((a+1)%(b+1))
    --            = Nat.gcd (b+1) ((a+1)%(b+1)) [by IH]
    --            = Nat.gcd (a+1) (b+1) [by gcd_rec + gcd_comm]
    -- Note: Nat.gcd_rec m n : Nat.gcd m n = Nat.gcd (n % m) m
    simp only [lehmerGcd, if_pos hge]
    rw [ih]
    -- Goal: (b+1).gcd ((a+1)%(b+1)) = (a+1).gcd (b+1)
    -- gcd_comm: (b+1).gcd ((a+1)%(b+1)) = ((a+1)%(b+1)).gcd (b+1)
    -- ←gcd_rec applied to (b+1, a+1): ((a+1)%(b+1)).gcd (b+1) = (b+1).gcd (a+1)
    -- gcd_comm: (b+1).gcd (a+1) = (a+1).gcd (b+1)
    rw [Nat.gcd_comm (b + 1) _, ← Nat.gcd_rec, Nat.gcd_comm]
  | case4 a b hlt ih =>
    -- a+1 < b+1: lehmerGcd (a+1) (b+1) = lehmerGcd (a+1) ((b+1)%(a+1))
    --            = Nat.gcd (a+1) ((b+1)%(a+1)) [by IH]
    --            = Nat.gcd (a+1) (b+1) [by gcd_rec]
    simp only [lehmerGcd, if_neg hlt]
    rw [ih]
    -- Goal: (a+1).gcd ((b+1)%(a+1)) = (a+1).gcd (b+1)
    -- Nat.gcd_rec (a+1) (b+1): (a+1).gcd (b+1) = ((b+1)%(a+1)).gcd (a+1)
    -- So RHS = ((b+1)%(a+1)).gcd (a+1) = (a+1).gcd ((b+1)%(a+1)) by gcd_comm
    conv_rhs => rw [Nat.gcd_rec]
    exact Nat.gcd_comm _ _

-- ══════════════════════════════════════════════════════════════
-- § 6. Corollaries
-- ══════════════════════════════════════════════════════════════

/-- lehmerGcd is commutative (since Nat.gcd is). -/
theorem lehmerGcd_comm (a b : ℕ) : lehmerGcd a b = lehmerGcd b a := by
  rw [lehmerGcd_correct, lehmerGcd_correct, Nat.gcd_comm]

/-- lehmerGcd divides both inputs. -/
theorem lehmerGcd_dvd_left (a b : ℕ) : lehmerGcd a b ∣ a := by
  rw [lehmerGcd_correct]; exact Nat.gcd_dvd_left a b

theorem lehmerGcd_dvd_right (a b : ℕ) : lehmerGcd a b ∣ b := by
  rw [lehmerGcd_correct]; exact Nat.gcd_dvd_right a b

/-- lehmerGcd is the greatest: any common divisor divides lehmerGcd. -/
theorem dvd_lehmerGcd {a b d : ℕ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ lehmerGcd a b := by
  rw [lehmerGcd_correct]; exact Nat.dvd_gcd ha hb

/-- lehmerGcd 0 n = n. -/
@[simp] theorem lehmerGcd_zero_left (n : ℕ) : lehmerGcd 0 n = n := by
  simp [lehmerGcd_correct]

/-- lehmerGcd n 0 = n. -/
@[simp] theorem lehmerGcd_zero_right (n : ℕ) : lehmerGcd n 0 = n := by
  simp [lehmerGcd_correct]

-- ══════════════════════════════════════════════════════════════
-- § 7. Computational Verification
-- ══════════════════════════════════════════════════════════════

-- Verify against Nat.gcd on small examples
example : lehmerGcd 12 8 = 4 := by simp [lehmerGcd_correct]
example : lehmerGcd 35 21 = 7 := by simp [lehmerGcd_correct]
example : lehmerGcd 100 75 = 25 := by simp [lehmerGcd_correct]
example : lehmerGcd 89 55 = 1 := by simp [lehmerGcd_correct]

-- Verify progress on specific examples
example : (lehmerStep 12 8).1 + (lehmerStep 12 8).2 < 12 + 8 :=
  lehmerGcd_progress 12 8 (by norm_num) (by norm_num)

example : (lehmerStep 100 75).1 + (lehmerStep 100 75).2 < 100 + 75 :=
  lehmerGcd_progress 100 75 (by norm_num) (by norm_num)

-- GCD invariance under Lehmer step
example : Nat.gcd (lehmerStep 12 8).1 (lehmerStep 12 8).2 = Nat.gcd 12 8 :=
  lehmerStep_gcd_invariant 12 8

/-! ## Summary

**Proved (0 axioms, 0 sorries):**

1. `lehmerStep_gcd_invariant`: The Lehmer step preserves GCD.
   This is the mathematical core — each step maintains the invariant.

2. `lehmerGcd_progress`: Each step strictly decreases a + b when 0 < b ≤ a.
   This guarantees termination.

3. `lehmerGcd_correct`: The Lehmer GCD algorithm computes Nat.gcd.
   Proved by well-founded induction using `Nat.gcd_rec`.

**Connection to parent (BinaryGcdOQ03)**:
The parent proves GCD invariance under general det ±1 cofactor matrices, which
generalizes the single-step invariance here. The Lehmer-Schönhage hybrid applies
many Euclidean steps at once via cofactor matrices; the correctness of each such
batch follows from the same det ±1 argument.

**Open question (OQ-02)**: Can we prove the full hybrid Lehmer-Schönhage
`lehmerGcd` from `BinaryGcdOQ03.lean` equals `Nat.gcd`? The additional challenge
is the cofactor matrix application with `natAbs` and the termination argument.
-/

end LehmerGcdOQ01
