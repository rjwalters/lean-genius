import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Open Question 3 from "Infinitely Many Primes ≡ 3 (mod 4)"

## What This Proves

This entry answers Open Question 3 from the `infinitude-primes-4k3` gallery proof:

> *Prove the infinitude of primes ≡ 1 (mod 4) elementarily using Fermat's theorem
> that -1 is a quadratic residue mod p iff p ≡ 1 (mod 4).*

We prove there are infinitely many primes congruent to 1 modulo 4, using an
elementary argument via Euler's criterion for quadratic residues.

## Relationship to infinitude-primes-4k1

This is the same result as `infinitude-primes-4k1`, presented as the answer
to the open question from the companion 3 (mod 4) proof. The proofs are
structured identically; the key insight is the asymmetry:

- **p ≡ 3 (mod 4)**: elementary product argument (no QR theory needed)
- **p ≡ 1 (mod 4)**: requires Euler's criterion (-1 is QR mod p iff p ≡ 1 mod 4)

## The Proof Idea

1. Given any n, consider N = (2 · (n+1)!)² + 1
2. N is odd and > 1, so has an odd prime factor p
3. Since p | k² + 1, -1 is a square mod p (k² ≡ -1 mod p)
4. Euler's criterion: -1 QR mod p iff p ≡ 1 (mod 4)
5. So p ≡ 1 (mod 4) and p > n (since p ≤ n forces p | 1, contradiction)

## Status
- [x] Complete proof, 0 sorries, 0 axioms
- [x] Answers OQ-03 from infinitude-primes-4k3

## Mathlib Dependencies
- `Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one` (from SumTwoSquares)
- `Nat.dvd_factorial`
- Basic ZMod arithmetic
-/

namespace InfinitudePrimes4k3OQ03

open Nat

/-! ## Key Lemma: Odd Primes Dividing k² + 1 Are ≡ 1 (mod 4) -/

/-- If an odd prime p divides k² + 1, then p ≡ 1 (mod 4).
    This is the crucial asymmetry: the condition forces -1 to be a quadratic
    residue mod p, and Euler's criterion characterizes this as p ≡ 1 (mod 4). -/
lemma prime_dvd_sq_add_one_mod_four {p k : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hdiv : p ∣ k ^ 2 + 1) : p % 4 = 1 := by
  have hsq : IsSquare (-1 : ZMod p) := by
    use (k : ZMod p)
    have hzero : ((k ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; exact hdiv
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hzero
    have h : (k : ZMod p) ^ 2 = -1 := by
      have : (k : ZMod p) ^ 2 + 1 = 0 := hzero
      calc (k : ZMod p) ^ 2 = (k : ZMod p) ^ 2 + 1 - 1 := by ring
        _ = 0 - 1 := by rw [this]
        _ = -1 := by ring
    rw [sq] at h; exact h.symm
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne3 := Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one hp (dvd_refl p) hsq
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨m, hm⟩ := hodd
    have : p ≥ 3 := by have := hp.two_le; omega
    omega
  rcases hmod with h1 | h3
  · exact h1
  · exact absurd h3 hne3

/-- Every odd number > 1 has an odd prime factor. -/
lemma exists_odd_prime_factor {n : ℕ} (hn : n > 1) (hodd : Odd n) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p ≠ 2 := by
  obtain ⟨p, hp_prime, hp_div⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  use p, hp_prime, hp_div
  intro hp2
  rw [hp2] at hp_div
  exact (Nat.odd_iff_not_even.mp hodd) (even_iff_two_dvd.mpr hp_div)

/-! ## Main Theorem -/

/-- **Infinitely many primes ≡ 1 (mod 4)** (Answer to OQ-03 from infinitude-primes-4k3)

Given any natural number n, there exists a prime p > n with p ≡ 1 (mod 4).
This answers the open question: the Euclid-style argument for p ≡ 3 does not
directly extend to p ≡ 1, because products of 3-mod-4 primes can be 1 mod 4.
The fix is to use N = (2·(n+1)!)² + 1, whose prime factors are forced to be
≡ 1 (mod 4) by Euler's quadratic residue criterion. -/
theorem infinitely_many_primes_1_mod_4 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 4 = 1 := by
  intro n
  let N := (2 * (n + 1).factorial) ^ 2 + 1
  have hN_odd : Odd N := by
    simp only [N]
    exact (Even.pow_of_ne_zero (even_two_mul _) (by omega)).add_one
  have hN_gt1 : N > 1 := by
    simp only [N]
    have h1 : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
    have h2 : (2 * (n + 1).factorial) ^ 2 ≥ 4 := by nlinarith
    omega
  obtain ⟨p, hp_prime, hp_div, hp_ne2⟩ := exists_odd_prime_factor hN_gt1 hN_odd
  use p
  refine ⟨hp_prime, ?_, prime_dvd_sq_add_one_mod_four hp_prime hp_ne2 hp_div⟩
  by_contra hpn
  push_neg at hpn
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
  have hp_dvd_2fact : p ∣ 2 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
  have hp_dvd_sq : p ∣ (2 * (n + 1).factorial) ^ 2 := by
    rw [sq]; exact dvd_mul_of_dvd_left hp_dvd_2fact _
  have hp_dvd_diff : p ∣ N - (2 * (n + 1).factorial) ^ 2 := Nat.dvd_sub' hp_div hp_dvd_sq
  have hN_sub : N - (2 * (n + 1).factorial) ^ 2 = 1 := by simp only [N]; omega
  exact hp_prime.not_dvd_one (hN_sub ▸ hp_dvd_diff)

/-- The set of primes ≡ 1 (mod 4) is infinite. -/
theorem primes_1_mod_4_infinite : Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 1} := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, hp_prime, hp_gt, hp_mod⟩ := infinitely_many_primes_1_mod_4 n
  exact ⟨p, ⟨hp_prime, hp_mod⟩, hp_gt⟩

end InfinitudePrimes4k3OQ03
