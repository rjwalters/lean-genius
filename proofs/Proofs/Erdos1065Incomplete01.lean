import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-
# Erdős #1065: A Structural Characterization of Form A Primes

## Research Problem: erdos-1065-incomplete-01

Erdős Problem #1065 asks whether there are infinitely many primes
`p = 2^k · q + 1` with `q` prime (call these **Form A** primes). The parent
formalization (`erdos-1065`) axiomatizes this infinitude conjecture and verifies
many individual examples and non-examples by hand.

This file supplies the missing **structural characterization** that those
case-by-case verifications were probing: a single decidable criterion deciding
Form A membership for every odd prime, expressed through the *odd part* of `p − 1`.

## Main result

Write `p − 1 = 2^a · m` with `m` odd (`m = ordCompl[2] (p−1)` is the odd part).
Then for an odd prime `p`:

  **`p` is a Form A prime  ⟺  `m = 1`  or  `m` is prime.**

* `m = 1` means `p − 1` is a power of two — i.e. `p` is a Fermat-type prime
  `2^a + 1`, which is Form A with `q = 2`.
* `m` prime means `p = 2^a · m + 1` directly, Form A with `q = m`.
* `m` odd *composite* (e.g. `p = 37`, `36 = 2² · 9`, `m = 9`) means `p` is
  **not** Form A.

This criterion subsumes the parent's whole family of example / non-example
verifications: deciding Form A reduces to a single primality test on the odd part
of `p − 1`.

## Status (0 axioms, 0 sorries)

Fully self-contained and elementary (no number-theoretic conjectures). The
Form A predicate is redefined locally so this file does not import the parent's
conjecture axiom.

## References
- Parent: erdos-1065 (Primes of the Form 2^k · q + 1), Guy's B46
-/

set_option linter.unusedVariables false

namespace Erdos1065Char

open Nat

/-- **Form A**: a prime `p` with `p = 2^k · q + 1` for some prime `q` and `k ≥ 0`.
    (Local copy of the parent's `IsTwoTimePrimePlusOne`, kept axiom-free.) -/
def IsFormA (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q k : ℕ, q.Prime ∧ p = 2 ^ k * q + 1

/-- The odd part of `p − 1`: `ordCompl[2] (p−1) = (p−1) / 2^{v₂(p−1)}`. -/
abbrev oddPart (p : ℕ) : ℕ := ordCompl[2] (p - 1)

/-- The 2-adic valuation of `p − 1`. -/
abbrev twoVal (p : ℕ) : ℕ := (p - 1).factorization 2

/-- Decomposition: `2^{twoVal p} · oddPart p = p − 1`. Unfolds `ordProj · ordCompl = self`. -/
theorem sub_one_eq (p : ℕ) : 2 ^ twoVal p * oddPart p = p - 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2

/-- **Core computation.** If `p − 1 = 2^a · m` with `m` odd, then the odd part of
    `p − 1` is exactly `m` (and its 2-adic valuation is `a`). This is the unique
    factoring of `p − 1` into a power of two times an odd number. -/
theorem oddPart_eq {p a m : ℕ} (hm : ¬ 2 ∣ m) (h : p - 1 = 2 ^ a * m) :
    oddPart p = m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  have hval : twoVal p = a := by
    rw [twoVal, h, Nat.factorization_mul (pow_ne_zero a two_ne_zero) hm0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  have hdec := sub_one_eq p
  rw [hval, h] at hdec
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hdec

-- ============================================================
-- PART 1: Sufficiency — m = 1 or m prime ⟹ Form A
-- ============================================================

/-- If the odd part of `p − 1` is itself prime, then `p` is Form A
    (`q = oddPart p`, `k = twoVal p`). Converse of the parent's `smooth_structure`. -/
theorem isFormA_of_oddPart_prime {p : ℕ} (hp : p.Prime)
    (hq : (oddPart p).Prime) : IsFormA p := by
  refine ⟨hp, oddPart p, twoVal p, hq, ?_⟩
  have h := sub_one_eq p
  have hp1 : 1 ≤ p := hp.one_lt.le
  omega

/-- If `p − 1` is a power of two (odd part `= 1`) and `p` is an odd prime, then `p` is a
    Fermat-type prime `2^a + 1`, which is Form A with `q = 2`. -/
theorem isFormA_of_oddPart_one {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h1 : oddPart p = 1) : IsFormA p := by
  refine ⟨hp, 2, twoVal p - 1, Nat.prime_two, ?_⟩
  have h := sub_one_eq p
  rw [h1, mul_one] at h
  -- h : 2 ^ twoVal p = p - 1
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    have hpar := Nat.odd_iff.mp hodd
    omega
  have hval : 1 ≤ twoVal p := by
    rcases Nat.eq_zero_or_pos (twoVal p) with h0 | h0
    · rw [h0, pow_zero] at h; omega
    · exact h0
  have hpow : 2 ^ twoVal p = 2 ^ (twoVal p - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  omega

/-- **Sufficiency.** If the odd part of `p − 1` is `1` or prime, then the odd prime
    `p` is Form A. -/
theorem isFormA_of_oddPart {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : oddPart p = 1 ∨ (oddPart p).Prime) : IsFormA p :=
  h.elim (isFormA_of_oddPart_one hp hodd) (isFormA_of_oddPart_prime hp)

-- ============================================================
-- PART 2: Necessity — Form A ⟹ m = 1 or m prime
-- ============================================================

/-- **Necessity.** If `p = 2^k · q + 1` with `q` prime, then the odd part of `p − 1`
    is `1` (when `q = 2`) or prime (equal to `q`, when `q` is odd). -/
theorem oddPart_of_isFormA {p : ℕ} (h : IsFormA p) :
    oddPart p = 1 ∨ (oddPart p).Prime := by
  obtain ⟨hp, q, k, hq, heq⟩ := h
  have hsub : p - 1 = 2 ^ k * q := by omega
  rcases eq_or_ne q 2 with hq2 | hq2
  · -- q = 2: p − 1 = 2^(k+1) · 1, odd part is 1
    left
    have h' : p - 1 = 2 ^ (k + 1) * 1 := by rw [hsub, hq2, pow_succ]; ring
    exact oddPart_eq (m := 1) (by norm_num) h'
  · -- q odd prime: odd part = q
    right
    have hodd_q : ¬ 2 ∣ q := fun hdvd =>
      hq2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp hdvd).symm)
    rw [oddPart_eq hodd_q hsub]
    exact hq

-- ============================================================
-- PART 3: The characterization (decidable criterion)
-- ============================================================

/-- **Main theorem.** For an odd prime `p`, `p` is a Form A prime if and only if the odd
    part of `p − 1` is `1` (so `p − 1` is a power of two) or is itself prime.

    The right-hand side is decidable, so this turns the parent's case-by-case Form A
    verifications into a single primality test on the odd part of `p − 1`. -/
theorem isFormA_iff_oddPart {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    IsFormA p ↔ (oddPart p = 1 ∨ (oddPart p).Prime) :=
  ⟨oddPart_of_isFormA, isFormA_of_oddPart hp hodd⟩

-- ============================================================
-- PART 4: The criterion subsumes example / non-example verification
-- ============================================================

/-- `p = 37` is **not** Form A: `36 = 2² · 9`, odd part `9 = 3²` is composite. -/
theorem not_isFormA_37 : ¬ IsFormA 37 := by
  rw [isFormA_iff_oddPart (by norm_num) (by norm_num)]
  rw [oddPart_eq (a := 2) (m := 9) (by norm_num) (by norm_num)]
  decide

/-- `p = 41` is Form A: `40 = 2³ · 5`, odd part `5` is prime. -/
theorem isFormA_41 : IsFormA 41 := by
  rw [isFormA_iff_oddPart (by norm_num) (by norm_num)]
  rw [oddPart_eq (a := 3) (m := 5) (by norm_num) (by norm_num)]
  decide

/-- `p = 17` is Form A as a Fermat prime: `16 = 2⁴`, odd part `1`. -/
theorem isFormA_17 : IsFormA 17 := by
  rw [isFormA_iff_oddPart (by norm_num) (by norm_num)]
  rw [oddPart_eq (a := 4) (m := 1) (by norm_num) (by norm_num)]
  decide

/-- `p = 71` is not Form A: `70 = 2 · 35`, odd part `35 = 5 · 7` composite. -/
theorem not_isFormA_71 : ¬ IsFormA 71 := by
  rw [isFormA_iff_oddPart (by norm_num) (by norm_num)]
  rw [oddPart_eq (a := 1) (m := 35) (by norm_num) (by norm_num)]
  decide

end Erdos1065Char
