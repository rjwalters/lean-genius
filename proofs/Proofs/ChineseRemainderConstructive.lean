/-
# Chinese Remainder Theorem (Constructive)

This file formalizes the Chinese Remainder Theorem with an emphasis on constructive
proofs that provide explicit witnesses.

**Status**: DEEP DIVE
- Uses Mathlib's CRT infrastructure (Nat.chineseRemainder)
- Provides constructive versions with explicit computation
- Multiple moduli extension
- Concrete numerical examples with witnesses

**Chinese Remainder Theorem** (~3rd-5th century CE):
Given pairwise coprime moduli m₁, m₂, ..., mₖ and any integers a₁, a₂, ..., aₖ,
there exists a unique x (mod m₁m₂...mₖ) such that:
  x ≡ a₁ (mod m₁)
  x ≡ a₂ (mod m₂)
  ...
  x ≡ aₖ (mod mₖ)

**Named after**: The Sunzi Suanjing (孫子算經, "The Mathematical Classic of Sun Zi"),
a Chinese mathematical treatise from the 3rd-5th century CE.

**Historical Note**:
The classic problem: "Find a number that leaves remainder 2 when divided by 3,
remainder 3 when divided by 5, and remainder 2 when divided by 7."
Answer: 23 (unique mod 105 = 3 × 5 × 7)
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace ChineseRemainderConstructive

open Nat

/-!
## Core CRT for Two Moduli

The foundation: solving x ≡ a (mod m), x ≡ b (mod n) when gcd(m, n) = 1.
-/

/-- The Chinese Remainder Theorem (existence): for coprime moduli m and n,
    there exists a solution to any system of two congruences -/
theorem crt_exists (m n a b : ℕ) (hcoprime : Nat.Coprime m n) :
    ∃ x : ℕ, x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  let ⟨x, hx⟩ := Nat.chineseRemainder hcoprime a b
  exact ⟨x, hx.1, hx.2⟩

/-- The solution is unique modulo m * n -/
theorem crt_unique (m n a b x₁ x₂ : ℕ) (hcoprime : Nat.Coprime m n)
    (h1a : x₁ ≡ a [MOD m]) (h1b : x₁ ≡ b [MOD n])
    (h2a : x₂ ≡ a [MOD m]) (h2b : x₂ ≡ b [MOD n]) :
    x₁ ≡ x₂ [MOD m * n] := by
  have ha : x₁ ≡ x₂ [MOD m] := h1a.trans h2a.symm
  have hb : x₁ ≡ x₂ [MOD n] := h1b.trans h2b.symm
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp ⟨ha, hb⟩

/-- CRT with explicit bound: solution is less than m * n -/
theorem crt_bounded (m n a b : ℕ) (hcoprime : Nat.Coprime m n)
    (hm : 0 < m) (hn : 0 < n) :
    ∃ x : ℕ, x < m * n ∧ x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  let sol := Nat.chineseRemainder hcoprime a b
  refine ⟨sol.val, ?_, sol.property.1, sol.property.2⟩
  have hm' : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  exact Nat.chineseRemainder_lt_mul hcoprime a b hm' hn'

/-!
## Constructive Algorithm

The explicit formula uses Bézout's identity: if gcd(m,n) = 1,
then there exist u, v with mu + nv = 1.

The solution is: x = a·n·v + b·m·u (mod m·n)

Where:
- n·v ≡ 1 (mod m)  [so a·n·v ≡ a (mod m)]
- m·u ≡ 1 (mod n)  [so b·m·u ≡ b (mod n)]
-/

/-- Bézout coefficients for coprime naturals -/
def bezoutCoeffs (m n : ℕ) : ℤ × ℤ :=
  (Nat.gcdA m n, Nat.gcdB m n)

/-- Verify Bézout's identity holds -/
theorem bezout_identity (m n : ℕ) :
    m * Nat.gcdA m n + n * Nat.gcdB m n = Nat.gcd m n :=
  (Nat.gcd_eq_gcd_ab m n).symm

/-- When coprime, Bézout gives mu + nv = 1 -/
theorem bezout_coprime (m n : ℕ) (h : Nat.Coprime m n) :
    m * Nat.gcdA m n + n * Nat.gcdB m n = 1 := by
  rw [bezout_identity, h]
  simp

/-- The explicit CRT solution formula -/
def crtSolution (m n a b : ℕ) : ℤ :=
  let u := Nat.gcdA m n
  let v := Nat.gcdB m n
  a * n * v + b * m * u

/-!
## Concrete Examples with Explicit Witnesses

The classic example from Sunzi Suanjing:
"Find N where N ≡ 2 (mod 3), N ≡ 3 (mod 5), N ≡ 2 (mod 7)"

Solution: N = 23 (unique mod 105)
-/

section Examples

/-- 3 and 5 are coprime -/
example : Nat.Coprime 3 5 := by decide

/-- 3 and 7 are coprime -/
example : Nat.Coprime 3 7 := by decide

/-- 5 and 7 are coprime -/
example : Nat.Coprime 5 7 := by decide

/-- Example: x ≡ 2 (mod 3), x ≡ 3 (mod 5)
    Solution: x = 8 (unique mod 15)
    Verify: 8 = 2·3 + 2 = 8, 8 = 1·5 + 3 = 8 ✓ -/
example : 8 ≡ 2 [MOD 3] := by native_decide
example : 8 ≡ 3 [MOD 5] := by native_decide
example : 8 < 3 * 5 := by norm_num

/-- Example: x ≡ 2 (mod 3), x ≡ 2 (mod 7)
    Solution: x = 2 (or 23 mod 21)
    Verify: 2 mod 3 = 2, 2 mod 7 = 2 ✓ -/
example : 2 ≡ 2 [MOD 3] := by native_decide
example : 2 ≡ 2 [MOD 7] := by native_decide

/-- The Sunzi problem: x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7)
    Solution: x = 23 (unique mod 105 = 3·5·7) -/
example : 23 ≡ 2 [MOD 3] := by native_decide
example : 23 ≡ 3 [MOD 5] := by native_decide
example : 23 ≡ 2 [MOD 7] := by native_decide
example : 23 < 3 * 5 * 7 := by norm_num

/-- Verification: 23 + 105 = 128 also satisfies all congruences -/
example : 128 ≡ 2 [MOD 3] := by native_decide
example : 128 ≡ 3 [MOD 5] := by native_decide
example : 128 ≡ 2 [MOD 7] := by native_decide

/-- Another example: x ≡ 1 (mod 4), x ≡ 2 (mod 5)
    Solution: x = 17 (unique mod 20) -/
example : Nat.Coprime 4 5 := by decide
example : 17 ≡ 1 [MOD 4] := by native_decide
example : 17 ≡ 2 [MOD 5] := by native_decide

/-- Large example: x ≡ 3 (mod 11), x ≡ 5 (mod 13)
    Solution: x = 135 (unique mod 143 = 11·13) -/
example : Nat.Coprime 11 13 := by decide
example : 135 ≡ 3 [MOD 11] := by native_decide
example : 135 ≡ 5 [MOD 13] := by native_decide
example : 135 < 11 * 13 := by norm_num

end Examples

/-!
## Extension to Multiple Moduli

For pairwise coprime moduli m₁, m₂, ..., mₖ, we can iteratively apply CRT.
-/

/-- CRT for three pairwise coprime moduli -/
theorem crt_three (m₁ m₂ m₃ a₁ a₂ a₃ : ℕ)
    (h12 : Nat.Coprime m₁ m₂) (h13 : Nat.Coprime m₁ m₃) (h23 : Nat.Coprime m₂ m₃) :
    ∃ x : ℕ, x ≡ a₁ [MOD m₁] ∧ x ≡ a₂ [MOD m₂] ∧ x ≡ a₃ [MOD m₃] := by
  -- First solve for m₁, m₂
  obtain ⟨y, hy1, hy2⟩ := crt_exists m₁ m₂ a₁ a₂ h12
  -- y satisfies first two, now solve with m₃
  have hcoprime : Nat.Coprime (m₁ * m₂) m₃ := Nat.Coprime.mul h13 h23
  obtain ⟨x, hx12, hx3⟩ := crt_exists (m₁ * m₂) m₃ y a₃ hcoprime
  -- x ≡ y (mod m₁·m₂) means x ≡ y (mod m₁) and x ≡ y (mod m₂)
  have hx1 : x ≡ a₁ [MOD m₁] := by
    have h := Nat.ModEq.of_mul_right m₂ hx12
    exact h.trans hy1
  have hx2 : x ≡ a₂ [MOD m₂] := by
    have h := Nat.ModEq.of_mul_left m₁ hx12
    exact h.trans hy2
  exact ⟨x, hx1, hx2, hx3⟩

/-- The three-moduli solution is unique mod m₁·m₂·m₃ -/
theorem crt_three_unique (m₁ m₂ m₃ a₁ a₂ a₃ x₁ x₂ : ℕ)
    (h12 : Nat.Coprime m₁ m₂) (h13 : Nat.Coprime m₁ m₃) (h23 : Nat.Coprime m₂ m₃)
    (hx1 : x₁ ≡ a₁ [MOD m₁] ∧ x₁ ≡ a₂ [MOD m₂] ∧ x₁ ≡ a₃ [MOD m₃])
    (hx2 : x₂ ≡ a₁ [MOD m₁] ∧ x₂ ≡ a₂ [MOD m₂] ∧ x₂ ≡ a₃ [MOD m₃]) :
    x₁ ≡ x₂ [MOD m₁ * m₂ * m₃] := by
  -- x₁ ≡ x₂ (mod mᵢ) for each i
  have ha : x₁ ≡ x₂ [MOD m₁] := hx1.1.trans hx2.1.symm
  have hb : x₁ ≡ x₂ [MOD m₂] := hx1.2.1.trans hx2.2.1.symm
  have hc : x₁ ≡ x₂ [MOD m₃] := hx1.2.2.trans hx2.2.2.symm
  -- Combine using CRT theorem
  have hab : x₁ ≡ x₂ [MOD m₁ * m₂] :=
    (Nat.modEq_and_modEq_iff_modEq_mul h12).mp ⟨ha, hb⟩
  have h123 : Nat.Coprime (m₁ * m₂) m₃ := Nat.Coprime.mul h13 h23
  exact (Nat.modEq_and_modEq_iff_modEq_mul h123).mp ⟨hab, hc⟩

/-!
## Applications

CRT is fundamental in:
1. **Modular Arithmetic**: Computing large products mod n by working mod prime factors
2. **Cryptography**: RSA uses CRT for efficient decryption
3. **Computer Science**: Representing large integers as residue systems
4. **Calendar Calculations**: Finding days when multiple cycles align
-/

/-- Application: Representing numbers via residues (RNS)
    The number 23 can be uniquely represented as (2, 3, 2) in the system (mod 3, mod 5, mod 7) -/
example : 23 % 3 = 2 := rfl
example : 23 % 5 = 3 := rfl
example : 23 % 7 = 2 := rfl

/-- Any number < 105 = 3·5·7 is uniquely determined by its residues mod 3, 5, 7 -/
theorem rns_unique (x y : ℕ) (hx : x < 105) (hy : y < 105)
    (h3 : x % 3 = y % 3) (h5 : x % 5 = y % 5) (h7 : x % 7 = y % 7) :
    x = y := by
  have hx3 : x ≡ y [MOD 3] := h3
  have hx5 : x ≡ y [MOD 5] := h5
  have hx7 : x ≡ y [MOD 7] := h7
  have h35 : Nat.Coprime 3 5 := by decide
  have h37 : Nat.Coprime 3 7 := by decide
  have h57 : Nat.Coprime 5 7 := by decide
  -- Use CRT uniqueness
  have h_all : x ≡ y [MOD 3 * 5 * 7] := by
    have h12 : x ≡ y [MOD 3 * 5] := (Nat.modEq_and_modEq_iff_modEq_mul h35).mp ⟨hx3, hx5⟩
    have h123 : Nat.Coprime (3 * 5) 7 := Nat.Coprime.mul h37 h57
    exact (Nat.modEq_and_modEq_iff_modEq_mul h123).mp ⟨h12, hx7⟩
  simp only [Nat.ModEq] at h_all
  have hprod : 3 * 5 * 7 = 105 := by norm_num
  rw [hprod] at h_all
  omega

/-!
## The Constructive Algorithm in Detail

For x ≡ a (mod m) and x ≡ b (mod n) with gcd(m,n) = 1:

1. Use extended Euclidean algorithm to find u, v with mu + nv = 1
2. Then x = a·n·v + b·m·u is a solution:
   - x ≡ a·n·v (mod m) since m | b·m·u
   - n·v = 1 - m·u ≡ 1 (mod m), so x ≡ a·1 = a (mod m)
   - Similarly x ≡ b (mod n)

Example: x ≡ 2 (mod 3), x ≡ 3 (mod 5)
- Find u, v with 3u + 5v = 1: u = 2, v = -1 works (3·2 + 5·(-1) = 1)
- x = 2·5·(-1) + 3·3·2 = -10 + 18 = 8
- Verify: 8 mod 3 = 2 ✓, 8 mod 5 = 3 ✓
-/

/-- Verify the Bézout coefficients for 3 and 5 -/
example : (3 : ℤ) * 2 + 5 * (-1) = 1 := by norm_num

/-- The explicit formula for the (3, 5) case -/
example : (2 : ℤ) * 5 * (-1) + 3 * 3 * 2 = 8 := by norm_num

/-!
## Historical Note

The Chinese Remainder Theorem is one of the oldest results in number theory.
The Sunzi Suanjing (3rd-5th century CE) presents it as a practical problem:

"There are certain things whose number is unknown. If we count them by threes,
we have two left over; by fives, we have three left over; and by sevens,
two are left over. How many things are there?"

The answer is 23, and any number of the form 23 + 105k works.

In Western mathematics, the theorem was rediscovered and generalized by
Leonhard Euler and Carl Friedrich Gauss.
-/

#check crt_exists
#check crt_unique
#check crt_bounded
#check crt_three
#check crtSolution

end ChineseRemainderConstructive
