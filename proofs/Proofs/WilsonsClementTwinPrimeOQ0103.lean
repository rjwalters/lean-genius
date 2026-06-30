import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-!
# Clement's twin-prime criterion (Wilson, OQ-01 OQ-03)

**Clement's theorem (1949).** For an odd `n ≥ 3`, the pair `(n, n+2)` consists of two
primes if and only if

  `4·((n-1)! + 1) + n ≡ 0  (mod n·(n+2))`.

This packages two instances of Wilson's theorem — at the moduli `n` and `n+2` — and fuses
them with the Chinese remainder theorem (here realised as the fact that coprime divisors of
a number divide it simultaneously iff their product does).

Mathlib provides the Wilson biconditional `Nat.prime_iff_fac_equiv_neg_one`
(`Prime n ↔ (n-1)! ≡ -1 mod n`) but has **no twin-prime / simultaneous-primality criterion**.
The two contributions here are:

* `factorial_succ_succ_cast`: the modular bridge `(n+1)! ≡ 2·(n-1)! (mod n+2)`, obtained from
  `n+1 ≡ -1` and `n ≡ -2` modulo `n+2`. This is what lets a *single* factorial `(n-1)!`
  control Wilson's congruence at *both* moduli.
* `clement_twin_prime`: the full biconditional criterion.

We restrict to odd `n` (equivalently `n ≥ 3` odd): every genuine twin-prime candidate `n ≥ 3`
is odd, and for even `n` the divisor `n·(n+2)` is a multiple of `4` that the criterion quantity
never meets, so the odd hypothesis discards only the degenerate composite branch. The oddness is
used exactly twice: to make `4` invertible mod `n` and `2` invertible mod `n+2`, and to give the
coprimality `gcd(n, n+2) = 1`.
-/

open Nat
open scoped Nat

namespace ClementTwinPrime

/-- The Clement criterion quantity `C(n) = 4·((n-1)! + 1) + n`. -/
def clementValue (n : ℕ) : ℕ := 4 * ((n - 1)! + 1) + n

/-- Natural-number factorial expansion: `(n+1)! = (n+1)·n·(n-1)!` for `n ≥ 1`. -/
theorem factorial_succ_eq (n : ℕ) (hn : 1 ≤ n) :
    (n + 1)! = (n + 1) * (n * (n - 1)!) := by
  rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (show n ≠ 0 by omega)]

/-- **Modular bridge.** Working modulo `n+2`, where `n+1 ≡ -1` and `n ≡ -2`, the factorial
`(n+1)!` collapses to `2·(n-1)!`. This is the key identity that lets the single factorial
`(n-1)!` carry Wilson's congruence at the modulus `n+2`. -/
theorem factorial_succ_succ_cast (n : ℕ) (hn : 1 ≤ n) :
    (((n + 1)! : ℕ) : ZMod (n + 2)) = 2 * (((n - 1)! : ℕ) : ZMod (n + 2)) := by
  have hncast : (n : ZMod (n + 2)) = -2 := by
    have h0 : ((n + 2 : ℕ) : ZMod (n + 2)) = 0 := ZMod.natCast_self (n + 2)
    push_cast at h0
    linear_combination h0
  rw [factorial_succ_eq n hn]
  push_cast
  rw [hncast]
  ring

variable {n : ℕ}

/-- **Clement's twin-prime criterion.** For odd `n ≥ 3`, the pair `(n, n+2)` is a pair of
primes iff `n·(n+2)` divides `4·((n-1)! + 1) + n`. -/
theorem clement_twin_prime (hn : 3 ≤ n) (hodd : Odd n) :
    (Nat.Prime n ∧ Nat.Prime (n + 2)) ↔ n * (n + 2) ∣ clementValue n := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (n + 2) := ⟨by omega⟩
  -- `4` is a unit mod `n` and `2` is a unit mod `n+2` (both from oddness of `n`).
  have hcop4 : Nat.Coprime 4 n := by
    have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hodd
    have h44 : (4 : ℕ) = 2 * 2 := by norm_num
    rw [h44, Nat.coprime_mul_iff_left]
    exact ⟨h2, h2⟩
  have h4u : IsUnit (4 : ZMod n) := by
    simpa using (ZMod.isUnit_iff_coprime 4 n).mpr hcop4
  have hcop2 : Nat.Coprime 2 (n + 2) := Nat.coprime_two_left.mpr (hodd.add_even even_two)
  have h2u : IsUnit (2 : ZMod (n + 2)) := by
    simpa using (ZMod.isUnit_iff_coprime 2 (n + 2)).mpr hcop2
  -- Bridge: `n ∣ C(n)` is exactly Wilson's congruence `(n-1)! ≡ -1 (mod n)`.
  have hA : n ∣ clementValue n ↔ (((n - 1)! : ℕ) : ZMod n) = -1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    unfold clementValue
    push_cast
    rw [ZMod.natCast_self n, add_zero, h4u.mul_right_eq_zero, add_eq_zero_iff_eq_neg]
  -- Bridge: `(n+2) ∣ C(n)` is exactly Wilson's congruence `(n+1)! ≡ -1 (mod n+2)`.
  have hncast2 : (n : ZMod (n + 2)) = -2 := by
    have h0 : ((n + 2 : ℕ) : ZMod (n + 2)) = 0 := ZMod.natCast_self (n + 2)
    push_cast at h0
    linear_combination h0
  have hval2 :
      ((clementValue n : ℕ) : ZMod (n + 2))
        = 2 * ((((n + 1)! : ℕ) : ZMod (n + 2)) + 1) := by
    rw [factorial_succ_succ_cast n (by omega)]
    unfold clementValue
    push_cast
    rw [hncast2]
    ring
  have hB : (n + 2) ∣ clementValue n ↔ (((n + 1)! : ℕ) : ZMod (n + 2)) = -1 := by
    rw [← ZMod.natCast_eq_zero_iff, hval2, h2u.mul_right_eq_zero, add_eq_zero_iff_eq_neg]
  -- Wilson's biconditional at each modulus.
  have hWn : Nat.Prime n ↔ (((n - 1)! : ℕ) : ZMod n) = -1 :=
    Nat.prime_iff_fac_equiv_neg_one (by omega)
  have hWn2 : Nat.Prime (n + 2) ↔ (((n + 1)! : ℕ) : ZMod (n + 2)) = -1 := by
    have h := Nat.prime_iff_fac_equiv_neg_one (show (n + 2) ≠ 1 by omega)
    have he : n + 2 - 1 = n + 1 := by omega
    rwa [he] at h
  -- Coprimality and the CRT split.
  have hcop : Nat.Coprime n (n + 2) := by
    have h := Nat.coprime_add_self_right.mpr (Nat.coprime_two_right.mpr hodd)
    rwa [Nat.add_comm 2 n] at h
  have hsplit :
      n * (n + 2) ∣ clementValue n ↔
        (n ∣ clementValue n ∧ (n + 2) ∣ clementValue n) := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right n (n + 2)).trans h, (dvd_mul_left (n + 2) n).trans h⟩
    · rintro ⟨h1, h2⟩
      exact hcop.mul_dvd_of_dvd_of_dvd h1 h2
  calc
    (Nat.Prime n ∧ Nat.Prime (n + 2))
        ↔ ((((n - 1)! : ℕ) : ZMod n) = -1 ∧ (((n + 1)! : ℕ) : ZMod (n + 2)) = -1) := by
          rw [hWn, hWn2]
    _ ↔ (n ∣ clementValue n ∧ (n + 2) ∣ clementValue n) := by rw [hA, hB]
    _ ↔ n * (n + 2) ∣ clementValue n := hsplit.symm

/-- The smallest twin pair `(3, 5)`: the criterion fires. `C(3) = 4·(2!+1)+3 = 15 = 3·5`. -/
example : (Nat.Prime 3 ∧ Nat.Prime 5) ↔ 3 * 5 ∣ clementValue 3 :=
  clement_twin_prime (by norm_num) (by norm_num)

end ClementTwinPrime
