/-
Erdős Problem #828: Totient Divisibility φ(n) | n + a

Source: https://erdosproblems.com/828
Status: OPEN

Statement:
For any integer a ∈ ℤ, are there infinitely many n such that φ(n) | n + a?

Key Cases:
- a = 0: φ(n) | n iff n ∈ {0, 1} or n = 2^a · 3^b (easy exercise)
- a = -1: φ(n) | n - 1 is Lehmer's conjecture (implies n is prime when n > 1)
- a = 1: φ(n) | n + 1 - many examples exist

Known Results:
- The a = 0 case is completely characterized
- Lehmer's conjecture (a = -1) remains open since 1932
- The general conjecture is attributed to Graham

References:
- Guy (2004), Problem B37
- Erdős [Er83]
- Lehmer (1932)
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open Nat Set

namespace Erdos828

/- ## Part I: Basic Definitions -/

/-- The set of n where φ(n) | n + a. -/
def totientDivisors (a : ℤ) : Set ℕ :=
  {n : ℕ | (totient n : ℤ) ∣ (n : ℤ) + a}

/- ## Part II: Special Case a = 0 -/

/-- Forward direction: φ(2^a · 3^b) | (2^a · 3^b) for a > 0.
    Proof: φ(2^a) = 2^(a-1), and for b > 0, φ(3^b) = 2·3^(b-1).
    So φ(2^a · 3^b) = 2^a · 3^(b-1) (or 2^(a-1) when b = 0), which divides n. -/
theorem totient_dvd_two_three_pow (a : ℕ) (ha : 0 < a) (b : ℕ) :
    totient (2 ^ a * 3 ^ b) ∣ 2 ^ a * 3 ^ b := by
  rcases b.eq_zero_or_pos with rfl | hb
  · -- b = 0: φ(2^a) = 2^(a-1) | 2^a
    simp only [pow_zero, mul_one]
    rw [Nat.totient_prime_pow Nat.prime_two ha]
    norm_num
    exact pow_dvd_pow 2 (Nat.pred_le a)
  · -- b > 0: φ(2^a · 3^b) = 2^a · 3^(b-1) | 2^a · 3^b
    have hcop : Nat.Coprime (2 ^ a) (3 ^ b) :=
      Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 3)
    have h2 : totient (2 ^ a) = 2 ^ (a - 1) := by
      rw [Nat.totient_prime_pow Nat.prime_two ha]; simp
    have h3 : totient (3 ^ b) = 3 ^ (b - 1) * 2 := by
      rw [Nat.totient_prime_pow Nat.prime_three hb]
    rw [Nat.totient_mul hcop, h2, h3]
    -- Goal: 2^(a-1) * (3^(b-1) * 2) | 2^a * 3^b
    suffices h : 2 ^ (a - 1) * (3 ^ (b - 1) * 2) = 2 ^ a * 3 ^ (b - 1) by
      rw [h]; exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 3 (Nat.pred_le b))
    rw [mul_comm (3 ^ (b - 1)) 2, ← mul_assoc, ← pow_succ,
        Nat.sub_add_cancel (show 1 ≤ a from by omega)]

/-- Characterization: φ(n) | n iff n ≤ 1 or n = 2^a · 3^b for some a > 0.
    The forward direction (←) is proved above as totient_dvd_two_three_pow.
    The backward direction (→) requires showing primes ≥ 5 can't divide n. -/
axiom totient_dvd_self_iff (n : ℕ) :
    totient n ∣ n ↔ n ≤ 1 ∨ ∃ a > 0, ∃ b : ℕ, n = 2^a * 3^b

/-- The set {n : φ(n) | n} is infinite.
Proved via the family 2^(k+1): φ(2^(k+1)) = 2^k divides 2^(k+1). -/
theorem totientDivisors_zero_infinite : (totientDivisors 0).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 2 ^ (k + 1))
  · intro k₁ k₂ h
    have := Nat.pow_right_injective (by norm_num : 1 < 2) h
    omega
  · intro k
    simp only [totientDivisors, Set.mem_setOf_eq, add_zero]
    have htot : totient (2 ^ (k + 1)) = 2 ^ k := by
      rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k + 1)]
      simp
    rw [htot]
    norm_cast
    exact pow_dvd_pow 2 (by omega)

/- ## Part III: Special Case a = -1 (Lehmer's Conjecture) -/

/--
Lehmer's Conjecture (1932, OPEN):
For n > 1, φ(n) | n - 1 if and only if n is prime.
The "if" direction is easy: φ(p) = p - 1 | p - 1.
The "only if" direction is open — no composite n > 1 is known with φ(n) | n - 1.
-/
def lehmerConjecture : Prop :=
  ∀ n : ℕ, n > 1 → (totient n ∣ n - 1 ↔ n.Prime)

/-- Every prime satisfies φ(p) | p - 1. -/
theorem prime_totient_dvd_pred (p : ℕ) (hp : p.Prime) : totient p ∣ p - 1 := by
  rw [totient_prime hp]

/-- There are infinitely many n with φ(n) | n - 1 (namely, all primes).
For prime p: φ(p) = p - 1 divides p + (-1) = p - 1. -/
theorem totientDivisors_neg_one_infinite : (totientDivisors (-1)).Infinite := by
  apply Set.Infinite.mono (s := setOf Nat.Prime)
  · intro p hp
    simp only [totientDivisors, Set.mem_setOf_eq]
    rw [totient_prime hp]
    have h1 : 1 ≤ p := hp.one_le
    exact ⟨1, by omega⟩
  · exact Nat.infinite_setOf_prime

/- ## Part IV: The Main Conjecture -/

/--
**Erdős Problem #828 (OPEN):**
For every integer a, there are infinitely many n such that φ(n) | n + a.
Attributed to Graham.
-/
def erdos828Conjecture : Prop :=
  ∀ a : ℤ, (totientDivisors a).Infinite

/- ## Part V: Structural Properties -/

/-- φ(n) is always even for n > 2.
Proved from Mathlib's `Nat.totient_even`. -/
theorem totient_even (n : ℕ) (hn : n > 2) : 2 ∣ totient n := by
  obtain ⟨k, hk⟩ := Nat.totient_even (show 3 ≤ n by omega)
  exact ⟨k, by omega⟩

/-- For prime p, φ(p) = p - 1 (Mathlib wrapper). -/
theorem totient_prime' (p : ℕ) (hp : p.Prime) : totient p = p - 1 :=
  totient_prime hp

/-- For prime power p^k, φ(p^k) = p^(k-1) · (p - 1).
Direct application of Mathlib's `Nat.totient_prime_pow`. -/
theorem totient_prime_pow_formula (p k : ℕ) (hp : p.Prime) (hk : k > 0) :
    totient (p^k) = p^(k-1) * (p - 1) :=
  Nat.totient_prime_pow hp hk

/- ## Part VI: Summary -/

/--
**Erdős Problem #828: Summary**

The a = 0 case is fully characterized: φ(n) | n iff n = 2^a · 3^b.
Both totientDivisors(0) and totientDivisors(-1) are infinite.
-/
theorem erdos_828_summary :
    (totientDivisors 0).Infinite ∧
    (totientDivisors (-1)).Infinite :=
  ⟨totientDivisors_zero_infinite, totientDivisors_neg_one_infinite⟩

end Erdos828
