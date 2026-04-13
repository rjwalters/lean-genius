/-
Legendre's Formula: p-adic Valuation of n! (Wilson's Theorem OQ-03)

Source: Classical number theory — Adrien-Marie Legendre, 1808.
Status: COMPLETE

Statement:
For a prime p and natural number n, the exact power of p dividing n! is:

  ν_p(n!) = ⌊n/p⌋ + ⌊n/p²⌋ + ⌊n/p³⌋ + ···

Equivalently (via digit sums in base p, the "digit-sum form"):

  (p - 1) · ν_p(n!) = n − S_p(n)

where S_p(n) = sum of the base-p digits of n.

## Connection to Wilson's Theorem
Wilson's theorem: (p-1)! ≡ -1 (mod p), so p ∤ (p-1)!, i.e., ν_p((p-1)!) = 0.
Legendre's formula gives an independent algebraic proof:

  Since p-1 < p, the only base-p digit of (p-1) is p-1 itself.
  So S_p(p-1) = p-1, and (p-1) · ν_p((p-1)!) = (p-1) - (p-1) = 0.
  Since p ≥ 2, p-1 ≥ 1, so ν_p((p-1)!) = 0.

This gives Wilson's "non-divisibility" as a consequence of Legendre's counting.

## What This Proves
- [x] Legendre's formula (digit-sum form):   (p-1) · ν_p(n!) = n - S_p(n)
- [x] Legendre's formula (Finset sum form):  ν_p(n!) = ∑_{i≥1} ⌊n/pⁱ⌋
- [x] Connection: ν_p((p-1)!) = 0 via Legendre (algebraic Wilson proof)
- [x] ν_p(p!) = 1 (p! divisible by exactly p¹)
- [x] p does not divide (p-1)! (forward direction of Wilson's theorem)
- [x] Upper bound: ν_p(n!) ≤ n / (p-1)
- [x] Characterization: ν_p(n!) = 0 ↔ n < p
- [x] Concrete computations: ν₂(10!), ν₃(9!), ν₅(25!), Wilson checks

## Mathlib Dependencies
- `sub_one_mul_padicValNat_factorial` : (p-1) * ν_p(n!) = n - S_p(n)
- `padicValNat_factorial` : ν_p(n!) = ∑ i ∈ Ico 1 b, ⌊n/pⁱ⌋
- `Nat.Prime.dvd_factorial` : p ∣ n! ↔ p ≤ n (for prime p)
- `padicValNat.prime_pow` : ν_p(p^n) = n
- `padicValNat.mul` : ν_p(m·n) = ν_p(m) + ν_p(n) (m,n ≠ 0)
- `padicValNat.le_of_dvd` : p^n ∣ m → n ≤ ν_p(m)
- `padicValNat.eq_zero_of_not_dvd` : ¬p ∣ m → ν_p(m) = 0
- `Nat.digits_def'` : recursive definition of base-p digits

Parent proof: WilsonsTheorem.lean
Open question answered: "What is the exact power of p dividing n!?"
-/

import Mathlib

namespace WilsonsTheoremLegendre

open Nat

/-! ## Legendre's Formula — Main Theorems -/

/-- **Legendre's Formula (digit-sum form)**: For a prime p and natural number n,
    the p-adic valuation of n! satisfies:
    (p - 1) · ν_p(n!) = n − S_p(n),
    where S_p(n) = (Nat.digits p n).sum is the sum of the base-p digits of n.

    This is a direct application of Mathlib's `sub_one_mul_padicValNat_factorial`. -/
theorem legendre_digit_sum (p n : ℕ) [hp : Fact p.Prime] :
    (p - 1) * padicValNat p n ! = n - (p.digits n).sum :=
  sub_one_mul_padicValNat_factorial n

/-- **Legendre's Formula (Finset sum form)**: For a prime p, natural number n,
    and any bound b with b > log_p(n):
    ν_p(n!) = ⌊n/p⌋ + ⌊n/p²⌋ + ⌊n/p³⌋ + ··· + ⌊n/p^{b-1}⌋.
    The sum vanishes once pⁱ > n. -/
theorem legendre_sum (p n b : ℕ) [hp : Fact p.Prime] (hb : p.log n < b) :
    padicValNat p n ! = ∑ i ∈ Finset.Ico 1 b, n / p ^ i :=
  padicValNat_factorial hb

/-! ## Key Infrastructure: Digit Representation of (p - 1) -/

/-- For a prime p ≥ 2, the digit representation of (p-1) in base p is the single digit [p-1],
    since 0 < p-1 < p means p-1 is a one-digit number in base p. -/
theorem digits_pred_prime (p : ℕ) (hp : p.Prime) : p.digits (p - 1) = [p - 1] := by
  have hp2 := hp.two_le
  rw [Nat.digits_def' hp.one_lt (by omega : 0 < p - 1)]
  simp [Nat.mod_eq_of_lt (by omega : p - 1 < p),
        Nat.div_eq_of_lt (by omega : p - 1 < p)]

/-- The digit sum of (p-1) in base p equals p-1. -/
theorem digit_sum_pred_prime (p : ℕ) (hp : p.Prime) :
    (p.digits (p - 1)).sum = p - 1 := by
  rw [digits_pred_prime p hp]; simp

/-! ## Wilson's Theorem via Legendre's Formula -/

/-- **Wilson's Theorem (Legendre Proof)**: For any prime p,
    the p-adic valuation of (p-1)! equals 0.

    **Proof**: Legendre's digit-sum formula gives:
    (p-1) · ν_p((p-1)!) = (p-1) - S_p(p-1).
    Since S_p(p-1) = p-1 (one single digit), the right side is 0.
    As p-1 ≥ 1, we conclude ν_p((p-1)!) = 0. -/
theorem legendre_wilson (p : ℕ) (hp : p.Prime) :
    padicValNat p (p - 1) ! = 0 := by
  haveI : Fact p.Prime := Fact.mk hp
  have h := legendre_digit_sum p (p - 1)
  rw [digit_sum_pred_prime p hp] at h
  simp only [Nat.sub_self] at h
  -- h : (p - 1) * padicValNat p (p - 1)! = 0
  exact (Nat.mul_eq_zero.mp h).resolve_left (Nat.sub_pos_of_lt hp.one_lt).ne'

/-- **Corollary**: A prime p does not divide (p-1)!.
    This is the "non-divisibility" direction of Wilson's theorem.
    Direct proof via `Nat.Prime.dvd_factorial`. -/
theorem prime_not_dvd_factorial_pred (p : ℕ) (hp : p.Prime) :
    ¬ p ∣ (p - 1) ! :=
  hp.dvd_factorial.not.mpr (Nat.not_le.mpr (Nat.sub_lt hp.pos Nat.one_pos))

/-! ## The p-adic Valuation of p! -/

/-- **ν_p(p!) = 1**: The factorial p! is divisible by p exactly once.
    Only the single factor p in {1, 2, ..., p} is divisible by p.

    **Proof**: p! = p · (p-1)!, and ν_p(p · (p-1)!) = ν_p(p) + ν_p((p-1)!) = 1 + 0 = 1. -/
theorem padic_val_p_factorial (p : ℕ) (hp : p.Prime) :
    padicValNat p p ! = 1 := by
  haveI hf : Fact p.Prime := Fact.mk hp
  -- Step 1: p! = p * (p-1)!
  have hfact : p ! = p * (p - 1) ! := by
    have h := Nat.factorial_succ (p - 1)
    rwa [Nat.sub_add_cancel hp.one_lt.le] at h
  -- Step 2: Multiplicativity of padicValNat
  rw [hfact, padicValNat.mul hp.ne_zero (Nat.factorial_pos _).ne']
  -- Step 3: ν_p(p) = 1, ν_p((p-1)!) = 0
  have hp_val : padicValNat p p = 1 := by
    simpa using @padicValNat.prime_pow p hf 1
  rw [hp_val, legendre_wilson p hp]

/-! ## Upper Bound on ν_p(n!) -/

/-- **Upper bound**: ν_p(n!) ≤ n / (p - 1).
    Follows from Legendre's digit-sum form: since S_p(n) ≥ 0,
    (p-1) · ν_p(n!) = n - S_p(n) ≤ n.
    Dividing by (p-1) gives the bound.

    **Asymptotics**: ν_p(n!) ~ n / (p-1) as n → ∞. -/
theorem padic_val_factorial_le (p n : ℕ) [hp : Fact p.Prime] :
    padicValNat p n ! ≤ n / (p - 1) := by
  have h := legendre_digit_sum p n
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  have hle : padicValNat p n ! * (p - 1) ≤ n := by
    calc padicValNat p n ! * (p - 1)
        = (p - 1) * padicValNat p n ! := mul_comm _ _
      _ = n - (p.digits n).sum := h
      _ ≤ n := Nat.sub_le _ _
  exact (Nat.le_div_iff_mul_le hp1).mpr hle

/-! ## Zero Characterization -/

/-- **Zero iff n < p**: For prime p, ν_p(n!) = 0 if and only if n < p.
    This is because all factors {1, ..., n} are less than p, hence coprime to p. -/
theorem padic_val_factorial_zero_iff (p n : ℕ) [hp : Fact p.Prime] :
    padicValNat p n ! = 0 ↔ n < p := by
  constructor
  · intro h
    -- If padicValNat p n! = 0, then p ∤ n!, so n < p by dvd_factorial
    by_contra hge
    push_neg at hge
    -- hge : p ≤ n, so p ∣ n!
    have hdvd : p ∣ n ! := hp.out.dvd_factorial.mpr hge
    -- Since p ∣ n! and n! ≠ 0, ν_p(n!) ≥ 1
    have h1 : 1 ≤ padicValNat p n ! := by
        obtain ⟨k, hk⟩ := hdvd
        have hk0 : k ≠ 0 := by
          intro hk0; rw [hk0, mul_zero] at hk
          exact absurd hk (Nat.factorial_pos n).ne'
        have hp_val : padicValNat p p = 1 := by
          simpa using @padicValNat.prime_pow p ‹_› 1
        rw [hk, padicValNat.mul hp.out.ne_zero hk0, hp_val]
        omega
    omega
  · intro hlt
    -- n < p means p ∤ n!, so ν_p(n!) = 0
    exact padicValNat.eq_zero_of_not_dvd
      (hp.out.dvd_factorial.not.mpr (Nat.not_le.mpr hlt))

/-! ## Concrete Computations -/

/-- ν₂(10!) = 8. Base-2 digits of 10 = 1010₂, digit sum = 2.
    Formula: 1·ν₂(10!) = 10 - 2 = 8. -/
example : padicValNat 2 (10 !) = 8 := by native_decide

/-- ν₂(8!) = 7. Base-2 digits of 8 = 1000₂, digit sum = 1.
    Formula: 1·ν₂(8!) = 8 - 1 = 7. -/
example : padicValNat 2 (8 !) = 7 := by native_decide

/-- ν₃(9!) = 4. Base-3 digits of 9 = 100₃, digit sum = 1.
    Formula: 2·ν₃(9!) = 9 - 1 = 8, so ν₃(9!) = 4. -/
example : padicValNat 3 (9 !) = 4 := by native_decide

/-- ν₅(25!) = 6. Base-5 digits of 25 = 100₅, digit sum = 1.
    Formula: 4·ν₅(25!) = 25 - 1 = 24, so ν₅(25!) = 6. -/
example : padicValNat 5 (25 !) = 6 := by native_decide

/-- ν₇(48!) = 6. Finset sum: ⌊48/7⌋ + ⌊48/49⌋ = 6 + 0 = 6. -/
example : padicValNat 7 (48 !) = 6 := by native_decide

/-- ν₇(49!) = 8. Finset sum: ⌊49/7⌋ + ⌊49/49⌋ + ⌊49/343⌋ = 7 + 1 + 0 = 8. -/
example : padicValNat 7 (49 !) = 8 := by native_decide

/-- Wilson check: ν₅(4!) = 0 (4 < 5, so 5 ∤ 4!) -/
example : padicValNat 5 (4 !) = 0 := by native_decide

/-- Wilson check: ν₇(6!) = 0 (6 < 7, so 7 ∤ 6!) -/
example : padicValNat 7 (6 !) = 0 := by native_decide

/-- Wilson check: ν₁₁(10!) = 0 (10 < 11, so 11 ∤ 10!) -/
example : padicValNat 11 (10 !) = 0 := by native_decide

/-- Wilson check: ν₁₃(12!) = 0 (12 < 13, so 13 ∤ 12!) -/
example : padicValNat 13 (12 !) = 0 := by native_decide

end WilsonsTheoremLegendre
