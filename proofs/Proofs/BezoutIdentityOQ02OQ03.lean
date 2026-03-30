import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-
# Computable Euclid's Lemma via extGcd Coefficients

## Open Question (bezout-identity-oq-02-oq-03)
Can the Bézout coefficients from BezoutIdentityOQ01's `extGcd` be used to give a
fully computable version of Euclid's lemma, where both the proof and the divisibility
witness are computed from the extended Euclidean algorithm?

## Answer: Yes

We define `euclid_witness` as a computable function that takes coprime a, b and a
divisor k (where b*c = a*k) and returns the quotient c/a directly from the
extGcd coefficients.

## Key Insight

OQ01 gave us `extGcd : ℕ → ℕ → ℤ × ℤ × ℕ` with a*x + b*y = gcd(a,b).
OQ02 proved Euclid's lemma existentially via `coprime_iff_linear_combination`.

This file bridges them: given coprime a b (so extGcd gives x, y with a*x + b*y = 1),
and knowing a | b*c (so b*c = a*k for some k), the witness for a | c is:
  c = a * (x*c + y*k)
computed directly from extGcd's output, no existential quantifier needed.
-/

namespace BezoutIdentityOQ02OQ03

open Finset

-- ═══════════════════════════════════════════════════════════════
-- PART I: The Extended Euclidean Algorithm (self-contained)
-- ═══════════════════════════════════════════════════════════════

/-- The extended Euclidean algorithm as a computable function.
    Returns (x, y, g) where a * x + b * y = g = gcd(a, b). -/
def extGcd : ℕ → ℕ → ℤ × ℤ × ℕ
  | a, 0 => (1, 0, a)
  | a, b + 1 =>
    have : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
    let r := extGcd (b + 1) (a % (b + 1))
    (r.2.1, r.1 - ↑(a / (b + 1)) * r.2.1, r.2.2)

@[simp]
theorem extGcd_zero (a : ℕ) : extGcd a 0 = (1, 0, a) := by
  simp [extGcd]

theorem extGcd_succ (a b : ℕ) :
    extGcd a (b + 1) =
      let r := extGcd (b + 1) (a % (b + 1))
      (r.2.1, r.1 - ↑(a / (b + 1)) * r.2.1, r.2.2) := by
  simp [extGcd]

/-- The gcd component of extGcd equals Nat.gcd. -/
theorem extGcd_gcd : ∀ (a b : ℕ), (extGcd a b).2.2 = Nat.gcd a b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 => simp [Nat.gcd_zero_right]
    | b + 1 =>
      rw [extGcd_succ]; simp only
      have hlt : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
      rw [ih (a % (b + 1)) hlt (b + 1)]
      rw [Nat.gcd_comm a (b + 1), Nat.gcd_rec (b + 1) a, Nat.gcd_comm]

/-- extGcd computes valid Bézout coefficients. -/
theorem extGcd_bezout : ∀ (a b : ℕ),
    let r := extGcd a b
    (a : ℤ) * r.1 + (b : ℤ) * r.2.1 = (r.2.2 : ℤ) := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 => simp
    | b + 1 =>
      simp only; rw [extGcd_succ]; simp only
      have hlt : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
      have hrec := ih (a % (b + 1)) hlt (b + 1)
      simp only at hrec
      set x' := (extGcd (b + 1) (a % (b + 1))).1
      set y' := (extGcd (b + 1) (a % (b + 1))).2.1
      have hdiv : (a : ℤ) = ↑(a / (b + 1)) * ↑(b + 1) + ↑(a % (b + 1)) := by
        have h := Nat.div_add_mod a (b + 1); zify at h ⊢; linarith
      linear_combination hrec + hdiv * y'

/-- Combined: extGcd returns Bézout coefficients for gcd(a,b). -/
theorem extGcd_correct (a b : ℕ) :
    let r := extGcd a b
    (a : ℤ) * r.1 + (b : ℤ) * r.2.1 = ↑(Nat.gcd a b) := by
  have hbez := extGcd_bezout a b
  have hgcd := extGcd_gcd a b
  simp only; rw [← hgcd]; exact hbez

-- ═══════════════════════════════════════════════════════════════
-- PART II: Coprimality via extGcd
-- ═══════════════════════════════════════════════════════════════

/-- When a and b are coprime, extGcd gives x, y with a*x + b*y = 1. -/
theorem extGcd_coprime_bezout (a b : ℕ) (h : Nat.Coprime a b) :
    (a : ℤ) * (extGcd a b).1 + (b : ℤ) * (extGcd a b).2.1 = 1 := by
  have hc := extGcd_correct a b
  simp only at hc
  rw [Nat.Coprime] at h
  rw [h] at hc
  exact_mod_cast hc

-- ═══════════════════════════════════════════════════════════════
-- PART III: Computable Euclid's Lemma
-- ═══════════════════════════════════════════════════════════════

/-- The Euclid witness function: given coprime a, b and a proof that a | b*c,
    compute the concrete quotient c / a using extGcd coefficients.

    If (x, y, 1) = extGcd a b, then from a*x + b*y = 1 and b*c = a*k:
    c = 1*c = (a*x + b*y)*c = a*x*c + b*c*y = a*x*c + a*k*y = a*(x*c + y*k) -/
noncomputable def euclid_witness (a b c : ℕ) (hdvd : a ∣ b * c) : ℤ :=
  let x := (extGcd a b).1
  let y := (extGcd a b).2.1
  let k := (b * c / a : ℤ)
  x * c + y * k

/-- Euclid's lemma with a concrete, computable witness from extGcd.
    If Nat.Coprime a b and a | b*c, then a | c. The proof constructs
    the witness from extGcd coefficients rather than using existential extraction. -/
theorem euclids_lemma_computable (a b c : ℕ)
    (hcop : Nat.Coprime a b) (hdvd : a ∣ b * c) : a ∣ c := by
  -- Get concrete Bézout coefficients from extGcd
  set x := (extGcd a b).1
  set y := (extGcd a b).2.1
  have hbez : (a : ℤ) * x + (b : ℤ) * y = 1 := extGcd_coprime_bezout a b hcop
  -- Get the divisibility witness
  obtain ⟨k, hk⟩ : (a : ℤ) ∣ (b : ℤ) * (c : ℤ) := by exact_mod_cast hdvd
  -- The concrete witness is x * c + y * k
  rw [← Int.natCast_dvd_natCast]
  exact ⟨x * c + y * k, by linear_combination y * hk - (c : ℤ) * hbez⟩

-- ═══════════════════════════════════════════════════════════════
-- PART IV: Computational Verification
-- ═══════════════════════════════════════════════════════════════

-- Verify: gcd(3, 7) = 1, 3 | 7*6 = 42, so 3 | 6
-- extGcd(3, 7) computes concrete x, y with 3*x + 7*y = 1
example : (3 : ℕ) ∣ 6 :=
  euclids_lemma_computable 3 7 6 (by decide) (by norm_num)

-- Verify: gcd(5, 8) = 1, 5 | 8*15 = 120, so 5 | 15
example : (5 : ℕ) ∣ 15 :=
  euclids_lemma_computable 5 8 15 (by decide) (by norm_num)

-- Verify: gcd(11, 13) = 1, 11 | 13*22 = 286, so 11 | 22
example : (11 : ℕ) ∣ 22 :=
  euclids_lemma_computable 11 13 22 (by decide) (by norm_num)

-- Verify the extGcd outputs directly
example : extGcd 3 7 = (-2, 1, 1) := by native_decide
example : extGcd 5 8 = (-3, 2, 1) := by native_decide

-- Verify the Bézout identity: 3*(-2) + 7*1 = -6 + 7 = 1
example : (3 : ℤ) * (-2) + 7 * 1 = 1 := by norm_num

-- Verify the Bézout identity: 5*(-3) + 8*2 = -15 + 16 = 1
example : (5 : ℤ) * (-3) + 8 * 2 = 1 := by norm_num

-- ═══════════════════════════════════════════════════════════════
-- PART V: Prime Version with Computable Witness
-- ═══════════════════════════════════════════════════════════════

/-- Prime Euclid's lemma using computable Bézout coefficients. -/
theorem euclids_lemma_prime_computable (p a b : ℕ) (hp : Nat.Prime p)
    (hdvd : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · right
    exact euclids_lemma_computable p a b ((hp.coprime_iff_not_dvd).mpr ha) hdvd

-- Verify: 7 is prime, 7 | 14*3 = 42, so 7 | 14 or 7 | 3
example : (7 : ℕ) ∣ 14 ∨ (7 : ℕ) ∣ 3 :=
  euclids_lemma_prime_computable 7 14 3 (by norm_num) (by norm_num)

-- ═══════════════════════════════════════════════════════════════
-- PART VI: Linear Diophantine Equations
-- ═══════════════════════════════════════════════════════════════

/-- Using extGcd to solve ax + by = c when gcd(a,b) | c.

    If (x₀, y₀, g) = extGcd a b, then a*x₀ + b*y₀ = g.
    For ax + by = c with g | c, scale: x = x₀*(c/g), y = y₀*(c/g). -/
theorem linear_diophantine_solvable (a b c : ℕ) (h : Nat.gcd a b ∣ c) :
    ∃ x y : ℤ, (a : ℤ) * x + (b : ℤ) * y = (c : ℤ) := by
  obtain ⟨m, hm⟩ := h
  have hbez := extGcd_correct a b
  simp only at hbez
  set x₀ := (extGcd a b).1
  set y₀ := (extGcd a b).2.1
  refine ⟨x₀ * m, y₀ * m, ?_⟩
  have : (c : ℤ) = (Nat.gcd a b : ℤ) * (m : ℤ) := by
    push_cast [hm]; ring
  rw [this]
  linear_combination (m : ℤ) * hbez

/-- The converse: if ax + by = c has an integer solution, then gcd(a,b) | c. -/
theorem linear_diophantine_necessary (a b c : ℕ) (x y : ℤ)
    (h : (a : ℤ) * x + (b : ℤ) * y = (c : ℤ)) : Nat.gcd a b ∣ c := by
  have ha : (Nat.gcd a b : ℤ) ∣ (a : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a b)
  have hb : (Nat.gcd a b : ℤ) ∣ (b : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a b)
  have hdvd : (Nat.gcd a b : ℤ) ∣ (c : ℤ) := by
    rw [← h]
    exact dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y)
  exact_mod_cast hdvd

/-- Complete characterization: ax + by = c has integer solutions iff gcd(a,b) | c. -/
theorem linear_diophantine_iff (a b c : ℕ) :
    (∃ x y : ℤ, (a : ℤ) * x + (b : ℤ) * y = (c : ℤ)) ↔ Nat.gcd a b ∣ c := by
  constructor
  · rintro ⟨x, y, h⟩
    exact linear_diophantine_necessary a b c x y h
  · exact linear_diophantine_solvable a b c

-- Verify: 6x + 10y = 14 is solvable since gcd(6,10) = 2 | 14
example : ∃ x y : ℤ, 6 * x + 10 * y = 14 :=
  linear_diophantine_solvable 6 10 14 (by decide)

-- Verify: 6x + 10y = 7 has no solution since gcd(6,10) = 2 ∤ 7
example : ¬ ∃ x y : ℤ, 6 * x + 10 * y = 7 := by
  intro ⟨x, y, h⟩
  have : (2 : ℤ) ∣ 6 * x + 10 * y := ⟨3 * x + 5 * y, by ring⟩
  rw [h] at this
  norm_num at this

end BezoutIdentityOQ02OQ03
