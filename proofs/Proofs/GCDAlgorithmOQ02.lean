/-
  GCD Algorithm OQ-02: Stein's Binary GCD Algorithm

  Stein's algorithm (1967) computes gcd(a,b) using only subtraction,
  comparison, and division by 2 (bit shift) — no general division.

  Algorithm:
  1. gcd(0, b) = b, gcd(a, 0) = a
  2. If both even: gcd(a, b) = 2 · gcd(a/2, b/2)
  3. If a even, b odd: gcd(a, b) = gcd(a/2, b)
  4. If a odd, b even: gcd(a, b) = gcd(a, b/2)
  5. If both odd: gcd(a, b) = gcd(|a-b|/2, min(a,b))

  Termination: In step 5, |a-b| < max(a,b), and the division by 2
  in other steps also reduces the problem.
-/
import Mathlib

namespace GCDAlgorithmOQ02

/-- Stein's binary GCD algorithm.
    Uses only subtraction and bit shifts (division by 2). -/
def binaryGcd : ℕ → ℕ → ℕ
  | 0, b => b
  | a, 0 => a
  | a + 1, b + 1 =>
    -- Both are ≥ 1, check parity
    if (a + 1) % 2 = 0 then
      if (b + 1) % 2 = 0 then
        -- Both even: factor out 2
        2 * binaryGcd ((a + 1) / 2) ((b + 1) / 2)
      else
        -- a even, b odd
        binaryGcd ((a + 1) / 2) (b + 1)
    else
      if (b + 1) % 2 = 0 then
        -- a odd, b even
        binaryGcd (a + 1) ((b + 1) / 2)
      else
        -- Both odd: subtract and halve
        if a + 1 ≤ b + 1 then
          binaryGcd ((b + 1 - (a + 1)) / 2) (a + 1)
        else
          binaryGcd ((a + 1 - (b + 1)) / 2) (b + 1)
  termination_by a + b

/-- The binary GCD computes the correct GCD. -/
theorem binaryGcd_eq_gcd (a b : ℕ) : binaryGcd a b = Nat.gcd a b := by
  sorry

/-- The binary GCD uses O(log(max(a,b))) steps. -/
-- This is because each step either halves one argument (steps 2-4)
-- or reduces the sum a+b by at least half (step 5).
-- Total steps ≤ 2·log₂(max(a,b)) + 1.

/-- Key lemma: both-even case preserves GCD.
    gcd(2a, 2b) = 2 · gcd(a, b). -/
theorem gcd_both_even (a b : ℕ) : Nat.gcd (2 * a) (2 * b) = 2 * Nat.gcd a b := by
  rw [Nat.gcd_mul_left]

/-- Key lemma: even-odd case preserves GCD.
    gcd(2a, 2b+1) = gcd(a, 2b+1). -/
theorem gcd_even_odd (a b : ℕ) : Nat.gcd (2 * a) (2 * b + 1) = Nat.gcd a (2 * b + 1) := by
  rw [Nat.Coprime.gcd_mul_left_cancel_right]
  exact Nat.coprime_two_left.mpr (by omega)

/-- Key lemma: both-odd case preserves GCD.
    For odd a ≤ b: gcd(a, b) = gcd((b-a)/2, a)
    since b-a is even (both odd) and 2 ∤ a. -/
theorem gcd_both_odd (a b : ℕ) (ha : Odd a) (hb : Odd b) (hab : a ≤ b) :
    Nat.gcd a b = Nat.gcd ((b - a) / 2) a := by
  sorry

end GCDAlgorithmOQ02
