import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-
# Binary GCD (Stein's Algorithm)

## What This Proves
Formalizes the Binary GCD algorithm (Stein, 1967), which computes GCD
using only subtraction and division by 2 (bit shifts), avoiding the
expensive division operation of the Euclidean algorithm.

The algorithm is based on three observations:
1. gcd(2a, 2b) = 2 · gcd(a, b)
2. gcd(2a, b) = gcd(a, b) when b is odd (since gcd(2, odd) = 1)
3. gcd(a - b, b) = gcd(a, b)

We define the algorithm and prove it equals Nat.gcd.

## Historical Context
Josef Stein published this algorithm in 1967, though it was known earlier
to Israeli programmers. On binary computers, division by 2 is a single
bit shift, making this significantly faster than Euclidean division for
large numbers. Modern implementations in GMP and other libraries use
variants of this algorithm.
-/

namespace BinaryGcd

/-! ## Part I: Key GCD Lemmas -/

/-- gcd(a - b, b) = gcd(a, b) when b ≤ a. -/
theorem gcd_sub_right {a b : ℕ} (h : b ≤ a) :
    Nat.gcd (a - b) b = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · -- gcd(a-b, b) | gcd(a, b): suffices to show gcd(a-b,b) | a and gcd(a-b,b) | b
    apply Nat.dvd_gcd
    · -- gcd(a-b, b) | a: since a = (a-b) + b
      have h1 := Nat.gcd_dvd_left (a - b) b
      have h2 := Nat.gcd_dvd_right (a - b) b
      have : a = (a - b) + b := by omega
      rw [this]; exact Nat.dvd_add h1 h2
    · exact Nat.gcd_dvd_right _ _
  · -- gcd(a, b) | gcd(a-b, b): suffices to show gcd(a,b) | (a-b) and gcd(a,b) | b
    apply Nat.dvd_gcd
    · exact Nat.dvd_sub' (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    · exact Nat.gcd_dvd_right _ _

/-- gcd(2a, b) = gcd(a, b) when b is odd (2 and b are coprime). -/
theorem gcd_mul_two_left {a b : ℕ} (hb : b % 2 = 1) :
    Nat.gcd (2 * a) b = Nat.gcd a b := by
  have hcop : Nat.Coprime 2 b := Nat.coprime_two_left.mpr hb
  exact (hcop.gcd_mul_left_cancel a).symm

/-- gcd(a, 2b) = gcd(a, b) when a is odd. -/
theorem gcd_mul_two_right {a b : ℕ} (ha : a % 2 = 1) :
    Nat.gcd a (2 * b) = Nat.gcd a b := by
  rw [Nat.gcd_comm, gcd_mul_two_left ha, Nat.gcd_comm]

/-- gcd(2a, 2b) = 2 · gcd(a, b). -/
theorem gcd_two_mul {a b : ℕ} :
    Nat.gcd (2 * a) (2 * b) = 2 * Nat.gcd a b :=
  Nat.gcd_mul_left 2 a b

/-! ## Part II: The Binary GCD Algorithm -/

/-- **Binary GCD (Stein's Algorithm)**:
Computes gcd using only subtraction and division by 2.

The algorithm:
- If either argument is 0, return the other
- If both even: extract factor of 2, recurse
- If one even, one odd: drop the factor of 2 (coprime with odd)
- If both odd: subtract smaller from larger, giving an even difference -/
def binaryGcd : ℕ → ℕ → ℕ
  | 0, b => b
  | a, 0 => a
  | a + 1, b + 1 =>
    -- Both nonzero
    if ha : (a + 1) % 2 = 0 then
      if hb : (b + 1) % 2 = 0 then
        -- Both even
        2 * binaryGcd ((a + 1) / 2) ((b + 1) / 2)
      else
        -- a+1 even, b+1 odd
        binaryGcd ((a + 1) / 2) (b + 1)
    else if hb : (b + 1) % 2 = 0 then
      -- a+1 odd, b+1 even
      binaryGcd (a + 1) ((b + 1) / 2)
    else if a + 1 > b + 1 then
      -- Both odd, a+1 > b+1: subtract and halve
      binaryGcd ((a + 1 - (b + 1)) / 2) (b + 1)
    else
      -- Both odd, a+1 ≤ b+1: subtract and halve
      binaryGcd (a + 1) ((b + 1 - (a + 1)) / 2)
  termination_by a + b
  decreasing_by all_goals omega

/-- When both a and b are odd and a > b, gcd((a-b)/2, b) = gcd(a, b).
    Proof: gcd(a-b, b) = gcd(a,b) by subtraction, and since a-b is even
    and b is odd, we can remove the factor of 2. -/
theorem gcd_odd_sub_half {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (hgt : a > b) :
    Nat.gcd ((a - b) / 2) b = Nat.gcd a b := by
  have hab_even : (a - b) % 2 = 0 := by omega
  have hab_eq : a - b = 2 * ((a - b) / 2) := by omega
  calc Nat.gcd ((a - b) / 2) b
      = Nat.gcd (2 * ((a - b) / 2)) b := (gcd_mul_two_left hb).symm
    _ = Nat.gcd (a - b) b := by rw [← hab_eq]
    _ = Nat.gcd a b := gcd_sub_right (le_of_lt hgt)

/-- Symmetric version: gcd(a, (b-a)/2) = gcd(a, b) when both odd, b ≥ a. -/
theorem gcd_odd_sub_half_right {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (hge : b ≥ a) :
    Nat.gcd a ((b - a) / 2) = Nat.gcd a b := by
  rw [Nat.gcd_comm, gcd_odd_sub_half hb ha (by omega), Nat.gcd_comm]

/-- **Correctness**: binaryGcd equals Nat.gcd.
    The proof uses the three key lemmas: factor extraction (gcd_two_mul),
    coprime reduction (gcd_mul_two_left), and odd subtraction (gcd_odd_sub_half).
    Each recursive case preserves the GCD invariant. -/
theorem binaryGcd_eq_gcd : ∀ a b : ℕ, binaryGcd a b = Nat.gcd a b := by
  intro a b
  -- Strong induction on a + b, matching the termination measure
  induction a, b using binaryGcd.induct with
  | case1 b =>
    -- binaryGcd 0 b = b = Nat.gcd 0 b
    simp [binaryGcd, Nat.gcd_zero_left]
  | case2 a =>
    -- binaryGcd (a+1) 0 = a+1 = Nat.gcd (a+1) 0
    simp [binaryGcd, Nat.gcd_zero_right]
  | case3 a b ha hb ih =>
    -- Both even: binaryGcd (a+1) (b+1) = 2 * binaryGcd ((a+1)/2) ((b+1)/2)
    simp only [binaryGcd, ha, hb, ↓reduceDIte]
    rw [ih]
    have ha2 : a + 1 = 2 * ((a + 1) / 2) := by omega
    have hb2 : b + 1 = 2 * ((b + 1) / 2) := by omega
    rw [ha2, hb2]; exact (gcd_two_mul).symm
  | case4 a b ha hb ih =>
    -- a+1 even, b+1 odd
    simp only [binaryGcd, ha, hb, ↓reduceDIte]
    rw [ih]
    have ha2 : a + 1 = 2 * ((a + 1) / 2) := by omega
    rw [ha2]; exact (gcd_mul_two_left hb).symm
  | case5 a b ha hb ih =>
    -- a+1 odd, b+1 even
    simp only [binaryGcd, ha, hb, ↓reduceDIte]
    rw [ih]
    have hb2 : b + 1 = 2 * ((b + 1) / 2) := by omega
    rw [hb2]; exact (gcd_mul_two_right ha).symm
  | case6 a b ha hb hgt ih =>
    -- Both odd, a+1 > b+1
    simp only [binaryGcd, ha, hb, hgt, ↓reduceDIte]
    rw [ih]
    exact gcd_odd_sub_half (by omega : (a + 1) % 2 = 1)
      (by omega : (b + 1) % 2 = 1) hgt
  | case7 a b ha hb hle ih =>
    -- Both odd, a+1 ≤ b+1
    simp only [binaryGcd, ha, hb, hle, ↓reduceDIte, show ¬(a + 1 > b + 1) from by omega]
    rw [ih]
    exact gcd_odd_sub_half_right (by omega : (a + 1) % 2 = 1)
      (by omega : (b + 1) % 2 = 1) (by omega : b + 1 ≥ a + 1)

/-! ## Part III: Basic Properties -/

/-- binaryGcd is commutative (follows from Nat.gcd_comm via correctness). -/
theorem binaryGcd_comm (a b : ℕ) : binaryGcd a b = binaryGcd b a := by
  rw [binaryGcd_eq_gcd, binaryGcd_eq_gcd, Nat.gcd_comm]

/-- binaryGcd 0 b = b. -/
theorem binaryGcd_zero_left (b : ℕ) : binaryGcd 0 b = b := by
  simp [binaryGcd]

/-- binaryGcd a 0 = a. -/
theorem binaryGcd_zero_right (a : ℕ) : binaryGcd a 0 = a := by
  cases a <;> simp [binaryGcd]

#check binaryGcd_eq_gcd

end BinaryGcd
