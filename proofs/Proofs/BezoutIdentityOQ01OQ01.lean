import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-
# Binary GCD (Stein's Algorithm) Correctness

## Open Question (bezout-identity-oq-01-oq-01)
Can Stein's binary GCD algorithm be formalized and proved equal to Nat.gcd?

## What This Proves
We define `binaryGcd` implementing Stein's binary GCD algorithm (1967) which
avoids modular division. We prove:
1. **Correctness**: binaryGcd a b = Nat.gcd a b
2. **Properties**: symmetric, divides both args, any common divisor divides it
3. **Bezout corollary**: binary GCD satisfies the same Bezout identity

## Algorithm Branches
1. gcd(0, b) = b
2. gcd(a, 0) = a
3. Both even: gcd(2a', 2b') = 2 * gcd(a', b')
4. a even, b odd: gcd(2a', b) = gcd(a', b)
5. a odd, b even: gcd(a, 2b') = gcd(a, b')
6. Both odd, a ≤ b: gcd(a, b) = gcd(a, (b-a)/2)  [b-a even, 2 ∤ a]
7. Both odd, a > b: gcd(a, b) = gcd((a-b)/2, b)
-/

namespace BezoutIdentityOQ01OQ01

open Nat

-- ═══════════════════════════════════════════════════════════════
-- PART I: GCD HELPER LEMMAS
-- ═══════════════════════════════════════════════════════════════

/-- gcd(2a, 2b) = 2 * gcd(a, b) -/
private lemma gcd_double_double (a b : ℕ) :
    Nat.gcd (2 * a) (2 * b) = 2 * Nat.gcd a b :=
  Nat.gcd_mul_left 2 a b

/-- If n is odd, 2 is coprime to n. -/
private lemma coprime_two_of_odd {n : ℕ} (hn : n % 2 = 1) : Nat.Coprime 2 n := by
  rw [Nat.coprime_comm]
  exact Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hn)

/-- If b is odd, gcd(2*a, b) = gcd(a, b). -/
private lemma gcd_two_mul_of_odd {b : ℕ} (hb : b % 2 = 1) (a : ℕ) :
    Nat.gcd (2 * a) b = Nat.gcd a b :=
  (coprime_two_of_odd hb).gcd_mul_left_cancel a

/-- If a is odd, gcd(a, 2*b) = gcd(a, b). -/
private lemma gcd_of_odd_two_mul {a : ℕ} (ha : a % 2 = 1) (b : ℕ) :
    Nat.gcd a (2 * b) = Nat.gcd a b := by
  rw [Nat.gcd_comm, gcd_two_mul_of_odd ha, Nat.gcd_comm]

/-- (b - a) % a = b % a when a ≤ b. -/
private lemma mod_sub_self {a b : ℕ} (h : a ≤ b) : (b - a) % a = b % a := by
  by_cases ha : a = 0
  · simp [ha]
  · conv_rhs => rw [← Nat.sub_add_cancel h, Nat.add_mod_right]

/-- gcd(a, b - a) = gcd(a, b) when a ≤ b. -/
private lemma gcd_sub_right {a b : ℕ} (h : a ≤ b) :
    Nat.gcd a (b - a) = Nat.gcd a b := by
  rw [Nat.gcd_rec a (b - a), Nat.gcd_rec a b, mod_sub_self h]

/-- When both a,b odd with a ≤ b: gcd(a, (b-a)/2) = gcd(a, b). -/
private lemma gcd_odd_sub_half {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (h : a ≤ b) :
    Nat.gcd a ((b - a) / 2) = Nat.gcd a b := by
  -- b - a is even (odd - odd), so b - a = 2 * ((b-a)/2)
  have hba : b - a = 2 * ((b - a) / 2) := by omega
  calc Nat.gcd a ((b - a) / 2)
      = Nat.gcd a (2 * ((b - a) / 2)) := (gcd_of_odd_two_mul ha _).symm
    _ = Nat.gcd a (b - a) := by rw [← hba]
    _ = Nat.gcd a b := gcd_sub_right h

/-- When both a,b odd with a > b: gcd((a-b)/2, b) = gcd(a, b). -/
private lemma gcd_odd_sub_half_left {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (h : b < a) :
    Nat.gcd ((a - b) / 2) b = Nat.gcd a b := by
  rw [Nat.gcd_comm, gcd_odd_sub_half hb ha (Nat.le_of_lt h), Nat.gcd_comm]

-- ═══════════════════════════════════════════════════════════════
-- PART II: BINARY GCD DEFINITION (STEIN'S ALGORITHM)
-- ═══════════════════════════════════════════════════════════════

/-- Stein's binary GCD algorithm. Terminates because a + b strictly decreases. -/
def binaryGcd (a b : ℕ) : ℕ :=
  if a = 0 then b
  else if b = 0 then a
  else if a % 2 = 0 ∧ b % 2 = 0 then 2 * binaryGcd (a / 2) (b / 2)
  else if a % 2 = 0 then binaryGcd (a / 2) b
  else if b % 2 = 0 then binaryGcd a (b / 2)
  else if a ≤ b then binaryGcd a ((b - a) / 2)
  else binaryGcd ((a - b) / 2) b
termination_by a + b
decreasing_by
  all_goals simp_wf
  all_goals omega

-- ═══════════════════════════════════════════════════════════════
-- PART III: CORRECTNESS THEOREM
-- ═══════════════════════════════════════════════════════════════

/-- Stein's binary GCD computes Nat.gcd.
    Proved by well-founded recursion matching the algorithm's structure. -/
theorem binaryGcd_eq_gcd (a b : ℕ) : binaryGcd a b = Nat.gcd a b := by
  unfold binaryGcd
  split_ifs with h1 h2 h3 h4 h5 h6
  · -- a = 0
    simp [h1]
  · -- a ≠ 0, b = 0
    simp [h2]
  · -- both even: 2 * binaryGcd (a/2) (b/2) = Nat.gcd a b
    obtain ⟨ha2, hb2⟩ := h3
    rw [binaryGcd_eq_gcd (a / 2) (b / 2)]
    -- Goal: 2 * Nat.gcd (a/2) (b/2) = Nat.gcd a b
    conv_rhs => rw [show a = 2 * (a / 2) from by omega,
                    show b = 2 * (b / 2) from by omega]
    exact (gcd_double_double (a / 2) (b / 2)).symm
  · -- a even, b odd: binaryGcd (a/2) b = Nat.gcd a b
    have hb1 : b % 2 = 1 := by omega
    rw [binaryGcd_eq_gcd (a / 2) b]
    -- Goal: Nat.gcd (a/2) b = Nat.gcd a b
    conv_rhs => rw [show a = 2 * (a / 2) from by omega]
    exact (gcd_two_mul_of_odd hb1 (a / 2)).symm
  · -- a odd, b even: binaryGcd a (b/2) = Nat.gcd a b
    have ha1 : a % 2 = 1 := by omega
    rw [binaryGcd_eq_gcd a (b / 2)]
    -- Goal: Nat.gcd a (b/2) = Nat.gcd a b
    conv_rhs => rw [show b = 2 * (b / 2) from by omega]
    exact (gcd_of_odd_two_mul ha1 (b / 2)).symm
  · -- both odd, a ≤ b: binaryGcd a ((b-a)/2) = Nat.gcd a b
    have ha1 : a % 2 = 1 := by omega
    have hb1 : b % 2 = 1 := by omega
    rw [binaryGcd_eq_gcd a ((b - a) / 2)]
    exact gcd_odd_sub_half ha1 hb1 h6
  · -- both odd, a > b: binaryGcd ((a-b)/2) b = Nat.gcd a b
    have ha1 : a % 2 = 1 := by omega
    have hb1 : b % 2 = 1 := by omega
    have hab : b < a := by omega
    rw [binaryGcd_eq_gcd ((a - b) / 2) b]
    exact gcd_odd_sub_half_left ha1 hb1 hab
termination_by a + b
decreasing_by
  all_goals simp_wf
  all_goals omega

-- ═══════════════════════════════════════════════════════════════
-- PART IV: PROPERTIES
-- ═══════════════════════════════════════════════════════════════

/-- Binary GCD is symmetric. -/
theorem binaryGcd_comm (a b : ℕ) : binaryGcd a b = binaryGcd b a := by
  simp only [binaryGcd_eq_gcd, Nat.gcd_comm]

/-- Binary GCD divides the left argument. -/
theorem binaryGcd_dvd_left (a b : ℕ) : binaryGcd a b ∣ a := by
  rw [binaryGcd_eq_gcd]; exact Nat.gcd_dvd_left a b

/-- Binary GCD divides the right argument. -/
theorem binaryGcd_dvd_right (a b : ℕ) : binaryGcd a b ∣ b := by
  rw [binaryGcd_eq_gcd]; exact Nat.gcd_dvd_right a b

/-- Any common divisor divides the binary GCD (universality). -/
theorem dvd_binaryGcd {k a b : ℕ} (ha : k ∣ a) (hb : k ∣ b) : k ∣ binaryGcd a b := by
  rw [binaryGcd_eq_gcd]; exact Nat.dvd_gcd ha hb

/-- Bézout identity: for any a, b there exist integer coefficients giving their binary GCD. -/
theorem bezout_via_binaryGcd (a b : ℕ) :
    ∃ x y : ℤ, (binaryGcd a b : ℤ) = a * x + b * y := by
  rw [binaryGcd_eq_gcd]
  refine ⟨Int.gcdA a b, Int.gcdB a b, ?_⟩
  have h := (Int.gcd_eq_gcd_ab (a : ℤ) (b : ℤ)).symm
  -- h : ↑(Int.gcd ↑a ↑b) = ↑a * gcdA ↑a ↑b + ↑b * gcdB ↑a ↑b
  have hcast : (Nat.gcd a b : ℤ) = ↑(Int.gcd (a : ℤ) (b : ℤ)) := by congr 1
  rw [hcast, h]

-- ═══════════════════════════════════════════════════════════════
-- PART V: COMPUTATIONAL VERIFICATION
-- ═══════════════════════════════════════════════════════════════

example : binaryGcd 12 8 = 4 := by native_decide
example : binaryGcd 35 15 = 5 := by native_decide
example : binaryGcd 17 5 = 1 := by native_decide
example : binaryGcd 252 198 = 18 := by native_decide
example : binaryGcd 1071 462 = Nat.gcd 1071 462 := by native_decide

end BezoutIdentityOQ01OQ01
