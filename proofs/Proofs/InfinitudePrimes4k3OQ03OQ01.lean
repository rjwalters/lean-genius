import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Infinitely Many Primes ≡ 1 (mod 3) via the cyclotomic Φ₃ Euclid argument
# (infinitude-primes-4k3-oq-03-oq-01)

## The Open Question

**OQ-03-OQ-01 from infinitude-primes-4k3**: The parent chain established infinitely many
primes ≡ 3 (mod 4) (product argument) and ≡ 1 (mod 4) (Euler's criterion for −1). Can a
*cyclotomic* Euclid-style argument prove infinitely many primes ≡ 1 (mod 3) using the third
cyclotomic polynomial Φ₃(x) = x² + x + 1?

## The Answer

**Yes.** This is the smallest genuinely "cyclotomic" instance of the Euclid argument. The key
fact about Φ₄(x) = x² + 1 used in the ≡ 1 (mod 4) case generalizes: a prime p dividing
Φ₃(m) = m² + m + 1 forces the multiplicative order of m mod p to be exactly 3 (unless p = 3),
and `orderOf m ∣ p − 1` then gives 3 ∣ p − 1, i.e. p ≡ 1 (mod 3).

## The Proof Idea

1. Given n, set m = 3 · (n+1)! and consider N = Φ₃(m) = m² + m + 1.
2. N ≥ 2, so N has a prime factor p.
3. **Coprimality**: p ∤ m, because p ∣ m would give p ∣ N − (m² + m) = 1.
   In particular p ≠ 3 (since 3 ∣ m) and p > n (since every prime ≤ n+1 divides (n+1)! ∣ m).
4. **Order argument**: m² + m + 1 ≡ 0 (mod p) ⟹ m³ ≡ 1 (mod p) (because
   (m − 1)(m² + m + 1) = m³ − 1). So `orderOf m ∣ 3`, hence `orderOf m ∈ {1, 3}`.
   - `orderOf m = 1` ⟹ m ≡ 1 ⟹ 3 ≡ 0 (mod p) ⟹ p = 3, contradiction.
   - So `orderOf m = 3`, and `orderOf m ∣ p − 1` (Fermat) gives 3 ∣ p − 1, i.e. p ≡ 1 (mod 3).
5. Hence for every n there is a prime p > n with p ≡ 1 (mod 3): infinitely many.

## Comparison with the mod-4 siblings

| | ≡ 3 (mod 4) | ≡ 1 (mod 4) | ≡ 1 (mod 3) (this file) |
|-|-------------|-------------|--------------------------|
| Polynomial | linear (4·k − 1) | Φ₄ = x² + 1 | Φ₃ = x² + x + 1 |
| Key fact | product of ≡1 stays ≡1 | −1 is a QR ⟺ p ≡ 1 (mod 4) | ord₃(m) = 3 ⟹ 3 ∣ p − 1 |
| Tool | parity of product | Euler's criterion | multiplicative order + Fermat |

The cyclotomic order argument is the prototype for the general statement "infinitely many
primes ≡ 1 (mod k) via Φ_k", specialized here to k = 3.

## Summary: 5 theorems, 0 new axioms, 0 sorries
-/

namespace InfinitudePrimes4k3OQ03OQ01

open Nat

/-! ## Key Lemma: primes dividing m² + m + 1 (other than 3) are ≡ 1 (mod 3) -/

/-- If a prime `p ≠ 3` divides `m² + m + 1 = Φ₃(m)`, then `p ≡ 1 (mod 3)`.

    Working mod `p`, the divisibility gives `m² + m + 1 = 0`, hence `m³ = 1`
    (since `(m − 1)(m² + m + 1) = m³ − 1`). Thus `orderOf m ∣ 3`, so the order is
    `1` or `3`. Order `1` would force `m = 1` and then `3 = 0 (mod p)`, i.e. `p = 3`;
    excluded. So the order is exactly `3`, and `orderOf m ∣ p − 1` (Fermat) yields
    `3 ∣ p − 1`, i.e. `p ≡ 1 (mod 3)`. -/
lemma prime_dvd_phi3_mod_three {p m : ℕ} (hp : Nat.Prime p) (hp3 : p ≠ 3)
    (hdiv : p ∣ m ^ 2 + m + 1) : p % 3 = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Reduce the divisibility to an equation in `ZMod p`.
  have hz : ((m ^ 2 + m + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have h0 : (m : ZMod p) ^ 2 + (m : ZMod p) + 1 = 0 := by push_cast at hz; linear_combination hz
  -- `m³ = 1` in `ZMod p`, because `(m − 1)(m² + m + 1) = m³ − 1`.
  have hcube : (m : ZMod p) ^ 3 = 1 := by linear_combination ((m : ZMod p) - 1) * h0
  -- `m ≠ 0` (else `0 = 1` in `ZMod p`).
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h; rw [h] at hcube; simp at hcube
  -- The order of `m` divides 3, so it is 1 or 3.
  have hord_dvd3 : orderOf (m : ZMod p) ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  rcases (Nat.dvd_prime Nat.prime_three).mp hord_dvd3 with hord1 | hord3
  · -- Order 1 ⟹ `m = 1` ⟹ `3 = 0 (mod p)` ⟹ `p = 3`: contradiction.
    rw [orderOf_eq_one_iff] at hord1
    rw [hord1] at h0
    norm_num at h0
    -- `h0 : (3 : ZMod p) = 0`, so `p ∣ 3`, so `p = 3`.
    have hp_dvd_3 : p ∣ 3 := by
      have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      exact (ZMod.natCast_eq_zero_iff 3 p).mp this
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp_dvd_3) hp3
  · -- Order 3, and `orderOf m ∣ p − 1` (Fermat) ⟹ `3 ∣ p − 1` ⟹ `p ≡ 1 (mod 3)`.
    have hdvd : orderOf (m : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hm0
    rw [hord3] at hdvd
    have hp2 : p ≥ 2 := hp.two_le
    omega

/-! ## The Main Theorem -/

/-- **THE MAIN THEOREM: Infinitely many primes ≡ 1 (mod 3)**

    Given any natural number `n`, there exists a prime `p > n` with `p ≡ 1 (mod 3)`.
    The witness is a prime factor of `N = Φ₃(3·(n+1)!) = (3·(n+1)!)² + 3·(n+1)! + 1`. -/
theorem infinitely_many_primes_1_mod_3 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 3 = 1 := by
  intro n
  set m := 3 * (n + 1).factorial with hm
  have hfac : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
  have hm3 : m ≥ 3 := by rw [hm]; omega
  -- `N = m² + m + 1 ≥ 2`, so it has a prime factor `p`.
  have hN_ne1 : m ^ 2 + m + 1 ≠ 1 := by nlinarith [hm3]
  obtain ⟨p, hp_prime, hp_div⟩ := Nat.exists_prime_and_dvd hN_ne1
  -- `p ∤ m`: otherwise `p ∣ (m² + m + 1) − (m² + m) = 1`.
  have hp_ndvd_m : ¬ p ∣ m := by
    intro hpm
    have h1 : p ∣ m ^ 2 + m := Nat.dvd_add (dvd_pow hpm two_ne_zero) hpm
    have hsub : m ^ 2 + m + 1 - (m ^ 2 + m) = 1 := by omega
    have : p ∣ 1 := by
      have := Nat.dvd_sub hp_div h1
      rwa [hsub] at this
    exact hp_prime.not_dvd_one this
  -- `p ≠ 3` since `3 ∣ m`.
  have hp_ne3 : p ≠ 3 := by
    intro h3
    exact hp_ndvd_m (h3 ▸ (by rw [hm]; exact dvd_mul_right 3 _))
  refine ⟨p, hp_prime, ?_, prime_dvd_phi3_mod_three hp_prime hp_ne3 hp_div⟩
  -- `p > n`: every prime `≤ n+1` divides `(n+1)! ∣ m`, contradicting `p ∤ m`.
  by_contra hle
  push_neg at hle
  apply hp_ndvd_m
  rw [hm]
  exact (Nat.dvd_factorial hp_prime.pos (by omega)).mul_left 3

/-! ## Consequences -/

/-- The set of primes `≡ 1 (mod 3)` is infinite. -/
theorem primes_1_mod_3_infinite : Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 3 = 1} := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, hp_prime, hp_gt, hp_mod⟩ := infinitely_many_primes_1_mod_3 n
  exact ⟨p, ⟨hp_prime, hp_mod⟩, hp_gt⟩

/-- There is no largest prime `≡ 1 (mod 3)`. -/
theorem no_largest_prime_1_mod_3 :
    ¬∃ p : ℕ, Nat.Prime p ∧ p % 3 = 1 ∧ ∀ q : ℕ, Nat.Prime q → q % 3 = 1 → q ≤ p := by
  intro ⟨p, _, _, hp_largest⟩
  obtain ⟨q, hq_prime, hq_gt, hq_mod⟩ := infinitely_many_primes_1_mod_3 p
  exact absurd (hp_largest q hq_prime hq_mod) (by omega)

/-! ## Examples -/

/-- 7 is a prime ≡ 1 (mod 3). -/
example : Nat.Prime 7 ∧ 7 % 3 = 1 := ⟨by decide, rfl⟩

/-- 13 is a prime ≡ 1 (mod 3). -/
example : Nat.Prime 13 ∧ 13 % 3 = 1 := ⟨by decide, rfl⟩

/-- 19 is a prime ≡ 1 (mod 3). -/
example : Nat.Prime 19 ∧ 19 % 3 = 1 := ⟨by decide, rfl⟩

/-- 31 is a prime ≡ 1 (mod 3). -/
example : Nat.Prime 31 ∧ 31 % 3 = 1 := ⟨by decide, rfl⟩

/-- 37 is a prime ≡ 1 (mod 3). -/
example : Nat.Prime 37 ∧ 37 % 3 = 1 := ⟨by decide, rfl⟩

#check @infinitely_many_primes_1_mod_3
#check @primes_1_mod_3_infinite
#check @no_largest_prime_1_mod_3

end InfinitudePrimes4k3OQ03OQ01
