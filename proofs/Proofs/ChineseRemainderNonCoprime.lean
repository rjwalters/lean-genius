/-
# Chinese Remainder Theorem for Non-Coprime Moduli

This file formalizes the generalized Chinese Remainder Theorem that works for
arbitrary moduli, not just coprime ones.

**The Generalized CRT**:
Given moduli m, n (not necessarily coprime) and integers a, b:
- The system x ≡ a (mod m), x ≡ b (mod n) has a solution
  if and only if gcd(m, n) ∣ (a - b)
- When a solution exists, it is unique modulo lcm(m, n)

This generalizes the classical CRT (which requires gcd(m, n) = 1).
When the moduli are coprime, gcd = 1 divides everything (solvability is automatic)
and lcm = m * n (uniqueness matches the classical statement).

**Historical Note**: While the coprime CRT dates to Sunzi Suanjing (3rd-5th century CE),
the non-coprime generalization was developed by Euler and later formalized in modern
number theory. It provides the complete characterization of solvability for simultaneous
linear congruences.
-/

import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace ChineseRemainderNonCoprime

open Nat Int

/-
## Combining Congruences via LCM

The fundamental property: if x ≡ y (mod m) and x ≡ y (mod n),
then x ≡ y (mod lcm(m, n)). This replaces the coprime condition in
the classical theorem modEq_and_modEq_iff_modEq_mul.
-/

/-- Lifting Nat.lcm_dvd to ℤ: if m and n both divide d in ℤ, so does lcm(m,n) -/
theorem int_natCast_lcm_dvd (m n : ℕ) (d : ℤ)
    (hm : (↑m : ℤ) ∣ d) (hn : (↑n : ℤ) ∣ d) :
    (↑(Nat.lcm m n) : ℤ) ∣ d := by
  rw [Int.natCast_dvd] at *
  exact Nat.lcm_dvd hm hn

/-- If a ≡ b (mod m) and a ≡ b (mod n), then a ≡ b (mod lcm(m,n)).
    This is the non-coprime generalization of the combining step in CRT. -/
theorem modEq_lcm_of_modEq {m n : ℕ} {a b : ℤ}
    (hm : a ≡ b [ZMOD ↑m]) (hn : a ≡ b [ZMOD ↑n]) :
    a ≡ b [ZMOD ↑(Nat.lcm m n)] := by
  rw [Int.modEq_iff_dvd] at *
  exact int_natCast_lcm_dvd m n (b - a) hm hn

/-- Converse: a congruence mod lcm implies congruence mod the left factor -/
theorem modEq_left_of_modEq_lcm {m n : ℕ} {a b : ℤ}
    (h : a ≡ b [ZMOD ↑(Nat.lcm m n)]) :
    a ≡ b [ZMOD ↑m] := by
  rw [Int.modEq_iff_dvd] at *
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left m n)) h

/-- Converse: a congruence mod lcm implies congruence mod the right factor -/
theorem modEq_right_of_modEq_lcm {m n : ℕ} {a b : ℤ}
    (h : a ≡ b [ZMOD ↑(Nat.lcm m n)]) :
    a ≡ b [ZMOD ↑n] := by
  rw [Int.modEq_iff_dvd] at *
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right m n)) h

/-- The full iff: a ≡ b mod lcm(m,n) ↔ a ≡ b mod m ∧ a ≡ b mod n -/
theorem modEq_lcm_iff {m n : ℕ} {a b : ℤ} :
    a ≡ b [ZMOD ↑(Nat.lcm m n)] ↔ a ≡ b [ZMOD ↑m] ∧ a ≡ b [ZMOD ↑n] :=
  ⟨fun h => ⟨modEq_left_of_modEq_lcm h, modEq_right_of_modEq_lcm h⟩,
   fun ⟨hm, hn⟩ => modEq_lcm_of_modEq hm hn⟩

/-
## Solvability Condition

The system x ≡ a (mod m), x ≡ b (mod n) is solvable if and only if gcd(m,n) | (a-b).
-/

/-- Necessity: if the system has a solution, then gcd(m,n) divides a - b -/
theorem noncoprime_crt_necessary (m n : ℕ) (a b : ℤ)
    (h : ∃ x : ℤ, x ≡ a [ZMOD ↑m] ∧ x ≡ b [ZMOD ↑n]) :
    (↑(Nat.gcd m n) : ℤ) ∣ (a - b) := by
  obtain ⟨x, hxm, hxn⟩ := h
  rw [Int.modEq_iff_dvd] at hxm hxn
  have hgm : (↑(Nat.gcd m n) : ℤ) ∣ (a - x) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left m n)) hxm
  have hgn : (↑(Nat.gcd m n) : ℤ) ∣ (b - x) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right m n)) hxn
  have h_diff : (↑(Nat.gcd m n) : ℤ) ∣ ((a - x) - (b - x)) := dvd_sub hgm hgn
  simp only [sub_sub_sub_cancel_right] at h_diff
  exact h_diff

/-- Sufficiency: if gcd(m,n) | (a-b), then the system has a solution.
    The construction uses Bézout's identity on m/gcd and n/gcd. -/
theorem noncoprime_crt_sufficient (m n : ℕ) (a b : ℤ)
    (hm : 0 < m) (_hn : 0 < n)
    (hgcd : (↑(Nat.gcd m n) : ℤ) ∣ (a - b)) :
    ∃ x : ℤ, x ≡ a [ZMOD ↑m] ∧ x ≡ b [ZMOD ↑n] := by
  set g := Nat.gcd m n with hg_def
  have hg_pos : 0 < g := Nat.pos_of_ne_zero (by
    intro heq
    have := Nat.gcd_eq_zero_iff.mp heq
    omega)
  set m' := m / g
  set n' := n / g
  have hm_eq : m = m' * g := by
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left m n)]
  have hn_eq : n = n' * g := by
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_right m n)]
  have hcoprime : Nat.Coprime m' n' := Nat.coprime_div_gcd_div_gcd hg_pos
  obtain ⟨k, hk⟩ := hgcd
  -- Bézout: ↑m' * s + ↑n' * t = 1 (since gcd(m', n') = 1)
  have hbezout : (↑m' : ℤ) * Int.gcdA (↑m') (↑n') +
      (↑n' : ℤ) * Int.gcdB (↑m') (↑n') = 1 := by
    have h := Int.gcd_eq_gcd_ab (↑m' : ℤ) (↑n' : ℤ)
    have hgcd1 : Int.gcd (↑m' : ℤ) (↑n' : ℤ) = 1 := by
      rw [Int.gcd]
      simp only [Int.natAbs_natCast]
      exact hcoprime
    rw [hgcd1] at h
    push_cast at h
    linarith
  set s := Int.gcdA (↑m' : ℤ) (↑n' : ℤ)
  set t := Int.gcdB (↑m' : ℤ) (↑n' : ℤ)
  -- Construct x = a + m * (-k * s)
  refine ⟨a + ↑m * (-k * s), ?_, ?_⟩
  · -- x ≡ a [ZMOD ↑m]: clear since a - x = m * (k * s)
    rw [Int.modEq_iff_dvd]
    show (↑m : ℤ) ∣ a - (a + ↑m * (-k * s))
    have : a - (a + ↑m * (-k * s)) = ↑m * (k * s) := by ring
    rw [this]
    exact dvd_mul_right _ _
  · -- x ≡ b [ZMOD ↑n]
    rw [Int.modEq_iff_dvd]
    show (↑n : ℤ) ∣ b - (a + ↑m * (-k * s))
    have hm_cast : (↑m : ℤ) = ↑m' * ↑g := by exact_mod_cast hm_eq
    have hn_cast : (↑n : ℤ) = ↑n' * ↑g := by exact_mod_cast hn_eq
    rw [hm_cast, hn_cast]
    -- Goal: ↑n' * ↑g ∣ b - (a + ↑m' * ↑g * (-k * s))
    -- hk : a - b = ↑g * k
    -- hbezout : ↑m' * s + ↑n' * t = 1
    -- Goal: ↑n' * ↑g ∣ b - (a + ↑m' * ↑g * (-k * s))
    -- Rewrite goal to show it equals ↑n' * ↑g * (-k * t)
    -- Step 1: b - (a + m'*g*(-k*s)) = (b - a) + m'*g*k*s  (ring)
    -- Step 2: = -g*k + m'*g*k*s  (using hk: a-b=g*k, so b-a=-g*k)
    -- Step 3: = g*k*(m'*s - 1)  (factor out g*k)
    -- Step 4: = g*k*(-(n'*t))  (using hbezout: m'*s = 1 - n'*t)
    -- Step 5: = -(n'*g*k*t) = n'*g*(-k*t)
    suffices key : b - (a + ↑m' * ↑g * (-k * s)) = ↑n' * ↑g * (-k * t) by
      rw [key]; exact dvd_mul_right _ _
    -- Use calc block for clarity
    calc b - (a + ↑m' * ↑g * (-k * s))
        = -(a - b) + ↑m' * (↑g * (k * s)) := by ring
      _ = -(↑g * k) + ↑m' * (↑g * (k * s)) := by rw [hk]
      _ = ↑g * k * (↑m' * s - 1) := by ring
      _ = ↑g * k * (-(↑n' * t)) := by
            congr 1
            linarith [hbezout]
      _ = ↑n' * ↑g * (-k * t) := by ring

/-- The full solvability characterization -/
theorem noncoprime_crt_iff (m n : ℕ) (a b : ℤ) (hm : 0 < m) (hn : 0 < n) :
    (∃ x : ℤ, x ≡ a [ZMOD ↑m] ∧ x ≡ b [ZMOD ↑n]) ↔
    (↑(Nat.gcd m n) : ℤ) ∣ (a - b) :=
  ⟨noncoprime_crt_necessary m n a b,
   noncoprime_crt_sufficient m n a b hm hn⟩

/-
## Uniqueness Modulo LCM

When a solution exists, it is unique modulo lcm(m, n).
-/

/-- If two values satisfy the same system of congruences, they agree mod lcm -/
theorem noncoprime_crt_unique (m n : ℕ) (a b x₁ x₂ : ℤ)
    (h1m : x₁ ≡ a [ZMOD ↑m]) (h1n : x₁ ≡ b [ZMOD ↑n])
    (h2m : x₂ ≡ a [ZMOD ↑m]) (h2n : x₂ ≡ b [ZMOD ↑n]) :
    x₁ ≡ x₂ [ZMOD ↑(Nat.lcm m n)] := by
  have hm : x₁ ≡ x₂ [ZMOD ↑m] := h1m.trans h2m.symm
  have hn : x₁ ≡ x₂ [ZMOD ↑n] := h1n.trans h2n.symm
  exact modEq_lcm_of_modEq hm hn

/-
## The Classical CRT as a Special Case

When gcd(m, n) = 1, the non-coprime CRT reduces to the classical CRT:
- Solvability: automatic (1 divides everything)
- Uniqueness: mod m * n (since lcm(m,n) = m * n when coprime)
-/

/-- The classical CRT is a special case: coprime moduli always have solutions -/
theorem classical_crt_from_general (m n : ℕ) (a b : ℤ)
    (hm : 0 < m) (hn : 0 < n) (hcoprime : Nat.Coprime m n) :
    ∃ x : ℤ, x ≡ a [ZMOD ↑m] ∧ x ≡ b [ZMOD ↑n] := by
  apply noncoprime_crt_sufficient m n a b hm hn
  rw [hcoprime]
  simp

/-- For coprime moduli, lcm = product, recovering the classical uniqueness -/
theorem coprime_lcm_eq_mul (m n : ℕ) (hcoprime : Nat.Coprime m n) :
    Nat.lcm m n = m * n :=
  Nat.Coprime.lcm_eq_mul hcoprime

/-- The complete classical CRT: coprime implies both solvability and uniqueness mod m*n -/
theorem noncoprime_crt_specializes (m n : ℕ) (a b : ℤ)
    (hm : 0 < m) (hn : 0 < n) (hcoprime : Nat.Coprime m n) :
    (∃ x : ℤ, x ≡ a [ZMOD ↑m] ∧ x ≡ b [ZMOD ↑n]) ∧
    Nat.lcm m n = m * n :=
  ⟨classical_crt_from_general m n a b hm hn hcoprime,
   coprime_lcm_eq_mul m n hcoprime⟩

/-
## Extension: Three Non-Coprime Moduli

For three moduli, necessary conditions are pairwise gcd divisibility.
-/

/-- Three moduli: pairwise gcd conditions are necessary -/
theorem noncoprime_crt_three_necessary (m₁ m₂ m₃ : ℕ) (a₁ a₂ a₃ : ℤ)
    (h : ∃ x : ℤ, x ≡ a₁ [ZMOD ↑m₁] ∧ x ≡ a₂ [ZMOD ↑m₂] ∧ x ≡ a₃ [ZMOD ↑m₃]) :
    (↑(Nat.gcd m₁ m₂) : ℤ) ∣ (a₁ - a₂) ∧
    (↑(Nat.gcd m₁ m₃) : ℤ) ∣ (a₁ - a₃) ∧
    (↑(Nat.gcd m₂ m₃) : ℤ) ∣ (a₂ - a₃) := by
  obtain ⟨x, h1, h2, h3⟩ := h
  exact ⟨noncoprime_crt_necessary m₁ m₂ a₁ a₂ ⟨x, h1, h2⟩,
         noncoprime_crt_necessary m₁ m₃ a₁ a₃ ⟨x, h1, h3⟩,
         noncoprime_crt_necessary m₂ m₃ a₂ a₃ ⟨x, h2, h3⟩⟩

/-- Three moduli: uniqueness via iterated LCM -/
theorem noncoprime_crt_three_unique (m₁ m₂ m₃ : ℕ) (a₁ a₂ a₃ x₁ x₂ : ℤ)
    (h1 : x₁ ≡ a₁ [ZMOD ↑m₁] ∧ x₁ ≡ a₂ [ZMOD ↑m₂] ∧ x₁ ≡ a₃ [ZMOD ↑m₃])
    (h2 : x₂ ≡ a₁ [ZMOD ↑m₁] ∧ x₂ ≡ a₂ [ZMOD ↑m₂] ∧ x₂ ≡ a₃ [ZMOD ↑m₃]) :
    x₁ ≡ x₂ [ZMOD ↑(Nat.lcm (Nat.lcm m₁ m₂) m₃)] := by
  have h12 : x₁ ≡ x₂ [ZMOD ↑(Nat.lcm m₁ m₂)] :=
    modEq_lcm_of_modEq (h1.1.trans h2.1.symm) (h1.2.1.trans h2.2.1.symm)
  have h3' : x₁ ≡ x₂ [ZMOD ↑m₃] := h1.2.2.trans h2.2.2.symm
  exact modEq_lcm_of_modEq h12 h3'

/-
## The LCM-Modulus Divides the Product-Modulus
-/

/-- lcm(m,n) always divides m * n -/
theorem lcm_dvd_mul (m n : ℕ) : Nat.lcm m n ∣ m * n :=
  Nat.lcm_dvd (dvd_mul_right m n) (dvd_mul_left n m)

/-- The non-coprime CRT gives a tighter uniqueness bound than naive product -/
theorem noncoprime_tighter_bound (m n : ℕ) (a b x₁ x₂ : ℤ)
    (h1m : x₁ ≡ a [ZMOD ↑m]) (h1n : x₁ ≡ b [ZMOD ↑n])
    (h2m : x₂ ≡ a [ZMOD ↑m]) (h2n : x₂ ≡ b [ZMOD ↑n]) :
    x₁ ≡ x₂ [ZMOD ↑(Nat.lcm m n)] :=
  noncoprime_crt_unique m n a b x₁ x₂ h1m h1n h2m h2n

/-
## Concrete Examples
-/

section Examples

-- Example 1: x ≡ 1 (mod 6), x ≡ 3 (mod 4)
-- gcd(6, 4) = 2, 2 | (1 - 3) = -2 ✓
-- Solution: x = 7, unique mod lcm(6,4) = 12
example : (7 : ℤ) ≡ 1 [ZMOD 6] := by decide
example : (7 : ℤ) ≡ 3 [ZMOD 4] := by decide
example : Nat.gcd 6 4 = 2 := by decide
example : Nat.lcm 6 4 = 12 := by decide
-- 7 + 12 = 19 also satisfies:
example : (19 : ℤ) ≡ 1 [ZMOD 6] := by decide
example : (19 : ℤ) ≡ 3 [ZMOD 4] := by decide

-- Example 2: x ≡ 1 (mod 6), x ≡ 2 (mod 4) — NO SOLUTION
-- gcd(6, 4) = 2, but 2 ∤ (1 - 2) = -1 ✗
example : ¬ ((2 : ℤ) ∣ (1 - 2)) := by decide

-- Example 3: x ≡ 3 (mod 6), x ≡ 5 (mod 10)
-- gcd(6, 10) = 2, 2 | (3 - 5) = -2 ✓
-- Solution: x = 15, unique mod lcm(6,10) = 30
example : (15 : ℤ) ≡ 3 [ZMOD 6] := by decide
example : (15 : ℤ) ≡ 5 [ZMOD 10] := by decide
example : Nat.gcd 6 10 = 2 := by decide
example : Nat.lcm 6 10 = 30 := by decide

-- Example 4: x ≡ 0 (mod 4), x ≡ 0 (mod 6)
-- gcd(4, 6) = 2, 2 | 0 ✓. Solution: x = 0, unique mod lcm(4,6) = 12
example : (0 : ℤ) ≡ 0 [ZMOD 4] := by decide
example : (0 : ℤ) ≡ 0 [ZMOD 6] := by decide

-- Example 5: Classical coprime case x ≡ 2 (mod 3), x ≡ 3 (mod 5)
-- gcd(3, 5) = 1, 1 | anything ✓. Solution: x = 8, unique mod lcm(3,5) = 15
example : (8 : ℤ) ≡ 2 [ZMOD 3] := by decide
example : (8 : ℤ) ≡ 3 [ZMOD 5] := by decide

end Examples

#check noncoprime_crt_necessary
#check noncoprime_crt_sufficient
#check noncoprime_crt_iff
#check noncoprime_crt_unique
#check modEq_lcm_of_modEq
#check modEq_lcm_iff
#check classical_crt_from_general

end ChineseRemainderNonCoprime
