import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-
# Extended Euclidean Algorithm as Computable Function

## Open Question (bezout-identity-oq-01)
Can the extended Euclidean algorithm itself be formalized as a computable function
with a correctness proof?

## What This Proves
We define `extGcd` as an explicit computable function implementing the extended
Euclidean algorithm, and prove:
1. **Bézout correctness**: The output (x, y, g) satisfies a * x + b * y = g
2. **GCD correctness**: The output g equals Nat.gcd a b
3. **Computability**: The function is fully computable (no axioms, no sorry)

## Approach
- Define `extGcd : ℕ → ℕ → ℤ × ℤ × ℕ` by well-founded recursion on b
- Use explicit projections instead of destructuring let (for definitional reduction)
- Prove correctness by well-founded induction matching the recursion
-/

namespace BezoutIdentityOQ01

/-
## The Extended Euclidean Algorithm

The algorithm computes gcd(a, b) together with Bézout coefficients x, y
such that a * x + b * y = gcd(a, b).
-/

/-- The extended Euclidean algorithm as a computable function.
    Returns (x, y, g) where a * x + b * y = g = gcd(a, b). -/
def extGcd : ℕ → ℕ → ℤ × ℤ × ℕ
  | a, 0 => (1, 0, a)
  | a, b + 1 =>
    have : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
    let r := extGcd (b + 1) (a % (b + 1))
    (r.2.1, r.1 - ↑(a / (b + 1)) * r.2.1, r.2.2)

/-- Extract the first Bézout coefficient. -/
def extGcdX (a b : ℕ) : ℤ := (extGcd a b).1

/-- Extract the second Bézout coefficient. -/
def extGcdY (a b : ℕ) : ℤ := (extGcd a b).2.1

/-- Extract the gcd from the extended Euclidean algorithm. -/
def extGcdG (a b : ℕ) : ℕ := (extGcd a b).2.2

-- Unfolding lemma for base case
@[simp]
theorem extGcd_zero (a : ℕ) : extGcd a 0 = (1, 0, a) := by
  simp [extGcd]

-- Unfolding lemma for recursive case
theorem extGcd_succ (a b : ℕ) :
    extGcd a (b + 1) =
      let r := extGcd (b + 1) (a % (b + 1))
      (r.2.1, r.1 - ↑(a / (b + 1)) * r.2.1, r.2.2) := by
  simp [extGcd]

/-
## GCD Correctness

The third component of extGcd equals Nat.gcd.
-/

/-- The gcd component of extGcd equals Nat.gcd.
    Proved by well-founded induction on b, matching the recursion of extGcd. -/
theorem extGcd_gcd : ∀ (a b : ℕ), (extGcd a b).2.2 = Nat.gcd a b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 =>
      simp [Nat.gcd_zero_right]
    | b + 1 =>
      rw [extGcd_succ]
      simp only
      have hlt : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
      have hrec := ih (a % (b + 1)) hlt (b + 1)
      rw [hrec]
      rw [Nat.gcd_comm a (b + 1), Nat.gcd_rec (b + 1) a, Nat.gcd_comm]

/-
## Bézout Correctness

The coefficients satisfy a * x + b * y = gcd(a, b).
-/

/-- The main correctness theorem: extGcd computes valid Bézout coefficients.
    For any a, b : ℕ, if (x, y, g) = extGcd a b, then ↑a * x + ↑b * y = ↑g. -/
theorem extGcd_bezout : ∀ (a b : ℕ),
    let r := extGcd a b
    (a : ℤ) * r.1 + (b : ℤ) * r.2.1 = (r.2.2 : ℤ) := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 =>
      simp
    | b + 1 =>
      simp only
      rw [extGcd_succ]
      simp only
      have hlt : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
      have hrec := ih (a % (b + 1)) hlt (b + 1)
      simp only at hrec
      set x' := (extGcd (b + 1) (a % (b + 1))).1
      set y' := (extGcd (b + 1) (a % (b + 1))).2.1
      set g := (extGcd (b + 1) (a % (b + 1))).2.2
      -- hrec : ↑(b + 1) * x' + ↑(a % (b + 1)) * y' = ↑g
      -- goal : ↑a * y' + ↑(b + 1) * (x' - ↑(a / (b + 1)) * y') = ↑g
      have hdiv : (a : ℤ) = ↑(a / (b + 1)) * ↑(b + 1) + ↑(a % (b + 1)) := by
        have h := Nat.div_add_mod a (b + 1)
        zify at h ⊢
        linarith
      linear_combination hrec + hdiv * y'

/-- Combined correctness: extGcd returns (x, y, gcd(a,b)) with a*x + b*y = gcd(a,b). -/
theorem extGcd_correct (a b : ℕ) :
    let r := extGcd a b
    (a : ℤ) * r.1 + (b : ℤ) * r.2.1 = ↑(Nat.gcd a b) := by
  have hbez := extGcd_bezout a b
  have hgcd := extGcd_gcd a b
  simp only
  rw [← hgcd]
  exact hbez

/-
## Computational Verification

We verify the algorithm produces correct results on concrete inputs.
-/

-- extGcd(12, 8) should give gcd = 4
example : (extGcd 12 8).2.2 = 4 := by native_decide

-- extGcd(35, 15) should give gcd = 5
example : (extGcd 35 15).2.2 = 5 := by native_decide

-- extGcd(17, 5) should give gcd = 1 (coprime)
example : (extGcd 17 5).2.2 = 1 := by native_decide

-- Verify Bézout identity for extGcd(12, 8)
example : let r := extGcd 12 8
          (12 : ℤ) * r.1 + 8 * r.2.1 = 4 := by native_decide

-- Verify Bézout identity for extGcd(35, 15)
example : let r := extGcd 35 15
          (35 : ℤ) * r.1 + 15 * r.2.1 = 5 := by native_decide

-- Verify Bézout identity for extGcd(17, 5)
example : let r := extGcd 17 5
          (17 : ℤ) * r.1 + 5 * r.2.1 = 1 := by native_decide

-- Verify with larger numbers: gcd(252, 198) = 18
example : (extGcd 252 198).2.2 = 18 := by native_decide

example : let r := extGcd 252 198
          (252 : ℤ) * r.1 + 198 * r.2.1 = 18 := by native_decide

/-
## Connection to Existing BezoutIdentity Module

Our computable extGcd agrees with Mathlib's gcdA/gcdB on the gcd component,
and provides an alternative way to compute Bézout coefficients.
-/

/-- extGcd produces the same gcd as Nat.gcd -/
theorem extGcd_gcd_eq (a b : ℕ) : extGcdG a b = Nat.gcd a b :=
  extGcd_gcd a b

/-- Bézout's identity via our computable extGcd -/
theorem bezout_via_extGcd (a b : ℕ) :
    ∃ x y : ℤ, (Nat.gcd a b : ℤ) = a * x + b * y := by
  exact ⟨extGcdX a b, extGcdY a b, by
    have h := extGcd_correct a b
    simp [extGcdX, extGcdY] at h ⊢
    linarith⟩

/-
## Properties of the Algorithm
-/

/-- The gcd output is always positive when a > 0 or b > 0. -/
theorem extGcd_gcd_pos (a b : ℕ) (h : a ≠ 0 ∨ b ≠ 0) :
    0 < (extGcd a b).2.2 := by
  rw [extGcd_gcd]
  exact Nat.pos_of_ne_zero (by
    intro hgcd
    rcases h with ha | hb
    · exact ha (Nat.eq_zero_of_gcd_eq_zero_left hgcd)
    · exact hb (Nat.eq_zero_of_gcd_eq_zero_right hgcd))

/-- The gcd output divides a. -/
theorem extGcd_gcd_dvd_left (a b : ℕ) : (extGcd a b).2.2 ∣ a := by
  rw [extGcd_gcd]
  exact Nat.gcd_dvd_left a b

/-- The gcd output divides b. -/
theorem extGcd_gcd_dvd_right (a b : ℕ) : (extGcd a b).2.2 ∣ b := by
  rw [extGcd_gcd]
  exact Nat.gcd_dvd_right a b

end BezoutIdentityOQ01
