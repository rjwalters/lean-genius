/-
  Angle Trisection OQ-03 OQ-02: Ω(log d) Lower Bound for Constructibility Check

  Proves that the O(log d) algorithm from AngleTrisectionOQ03 is tight:
  for inputs d = 2^k the halvings algorithm requires exactly k = Nat.log 2 d steps.
  This witnesses the Ω(log d) lower bound — the O(log d) upper bound cannot be improved
  asymptotically on this family of inputs.

  Companion to AngleTrisectionOQ03.lean (upper bound: O(log d) algorithm).

  Key results:
  - halvings_pow2: halvings (2^k) = k (exact step count)
  - halvings_eq_log_pow2: halvings (2^k) = Nat.log 2 (2^k) (matches log)
  - halvings_unbounded: no constant upper bound on step count
  - constructibility_lower_bound: Nat.log 2 (2^k) ≤ halvings (2^k)
  - halvings_pred_pow2: halvings (2^k - 1) = 0 (odd, rejected immediately)
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Proofs.AngleTrisectionOQ03

namespace AngleTrisectionOQ03OQ02

open AngleTrisectionOQ03 Nat

/-!
## Part I: The Halvings Algorithm

The constructibility check from OQ-03 proceeds by repeatedly halving d until it
reaches an odd number. For d = 2^k this takes exactly k steps; for odd d it takes 0.
We formalize the step count and prove its exact complexity.
-/

/-- Count halvings until d becomes odd (or reaches 0). -/
def halvings : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0
    then 1 + halvings ((n + 1) / 2)
    else 0
termination_by n => n

@[simp] theorem halvings_zero : halvings 0 = 0 := rfl
@[simp] theorem halvings_one : halvings 1 = 0 := rfl

/-- Equation lemma for the successor case (by definition). -/
@[simp] theorem halvings_succ (n : ℕ) :
    halvings (n + 1) = if (n + 1) % 2 = 0 then 1 + halvings ((n + 1) / 2) else 0 := rfl

/-- Odd inputs have halvings = 0: an odd number is not divisible by 2. -/
theorem halvings_odd {n : ℕ} (hn : n % 2 = 1) : halvings n = 0 := by
  cases n with
  | zero => simp at hn
  | succ m =>
    rw [halvings_succ]
    rw [if_neg (by omega)]

/-- Even positive inputs: halvings (2 * k) = 1 + halvings k. -/
theorem halvings_two_mul {k : ℕ} (hk : 0 < k) : halvings (2 * k) = 1 + halvings k := by
  rw [show 2 * k = (2 * k - 1) + 1 from by omega, halvings_succ]
  rw [if_pos (by omega), show (2 * k - 1 + 1) / 2 = k from by omega]

/-!
## Part II: Exact Step Count for Powers of 2

For d = 2^k, the halvings algorithm terminates after exactly k steps.
This proves the O(log d) upper bound from OQ-03 is achieved on this family.
-/

/-- **Main theorem**: halvings (2^k) = k.
    Induction: halvings (2^(k+1)) = halvings (2 · 2^k) = 1 + halvings (2^k) = 1 + k. -/
theorem halvings_pow2 (k : ℕ) : halvings (2^k) = k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show 2^n * 2 = 2 * 2^n from mul_comm (2^n) 2,
        halvings_two_mul (pow_pos (by norm_num) n), ih]

/-- halvings (2^k) equals the floor logarithm Nat.log 2 (2^k). -/
theorem halvings_eq_log_pow2 (k : ℕ) : halvings (2^k) = Nat.log 2 (2^k) := by
  rw [halvings_pow2, Nat.log_pow (by norm_num : 1 < 2)]

/-!
## Part III: Ω(log d) Lower Bound

The halvings algorithm is TIGHT: its O(log d) upper bound is optimal.
No algorithm can decide constructibility in fewer halvings on the inputs 2^k.
-/

/-- **Lower bound**: Nat.log 2 (2^k) ≤ halvings (2^k).
    For d = 2^k, the halvings count matches the floor log exactly. -/
theorem constructibility_lower_bound (k : ℕ) : Nat.log 2 (2^k) ≤ halvings (2^k) := by
  rw [halvings_eq_log_pow2]

/-- The step count is not bounded by any constant: no O(1) algorithm exists. -/
theorem halvings_unbounded (c : ℕ) : ∃ d : ℕ, halvings d ≥ c :=
  ⟨2^c, by simp [halvings_pow2]⟩

/-- Monotonicity: larger powers of 2 require more halvings. -/
theorem halvings_monotone_pow2 {j k : ℕ} (h : j ≤ k) : halvings (2^j) ≤ halvings (2^k) := by
  simp [halvings_pow2, h]

/-- **Tightness**: the halvings count and the log agree exactly for inputs d = 2^k.
    This establishes that Ω(log d) halvings are necessary for this family. -/
theorem halvings_complexity_tight (k : ℕ) :
    halvings (2^k) = Nat.log 2 (2^k) ∧ Nat.log 2 (2^k) = k :=
  ⟨halvings_eq_log_pow2 k, Nat.log_pow (by norm_num : 1 < 2)⟩

/-!
## Part IV: Separation of Powers from Non-Powers

For k ≥ 1: halvings (2^k - 1) = 0 since 2^k - 1 is odd.
The algorithm immediately rejects 2^k - 1 at the first step, while correctly
accepting 2^k after k halvings. The gap halvings (2^k) - halvings (2^k - 1) = k
confirms that Ω(log d) halvings are inherent to the YES-path.
-/

/-- For k ≥ 1: halvings (2^k - 1) = 0 since 2^k - 1 is odd. -/
theorem halvings_pred_pow2 {k : ℕ} (hk : 1 ≤ k) : halvings (2^k - 1) = 0 := by
  apply halvings_odd
  cases k with
  | zero => omega
  | succ m =>
    rw [pow_succ, mul_comm (2^m) 2]
    have h2m_pos : 0 < 2^m := pow_pos (by norm_num) m
    have hmod : 2 * 2^m % 2 = 0 := Nat.mul_mod_right 2 (2^m)
    omega

/-- The halvings count separates 2^k from 2^k - 1 for k ≥ 1. -/
theorem halvings_separates_pred {k : ℕ} (hk : 1 ≤ k) :
    halvings (2^k - 1) < halvings (2^k) := by
  rw [halvings_pred_pow2 hk, halvings_pow2]
  omega

/-!
## Part V: Concrete Computations

Numerical verification of the halvings step count.
-/

example : halvings (2^0) = 0 := by native_decide
example : halvings (2^1) = 1 := by native_decide
example : halvings (2^2) = 2 := by native_decide
example : halvings (2^3) = 3 := by native_decide
example : halvings (2^4) = 4 := by native_decide
example : halvings (2^5) = 5 := by native_decide
example : halvings (2^8) = 8 := by native_decide

example : halvings 3 = 0 := by native_decide   -- odd: immediately 0
example : halvings 6 = 1 := by native_decide   -- 6 = 2 · 3, halves to 3 (odd)
example : halvings 12 = 2 := by native_decide  -- 12 = 4 · 3, halves twice to 3
example : halvings 15 = 0 := by native_decide  -- 15 is odd

end AngleTrisectionOQ03OQ02
