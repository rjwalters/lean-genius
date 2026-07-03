/-
  Jacobi's Two-Square Count — the exact closed-form value of the divisor-character sum
  Open Question: fermat-two-squares-oq-04-oq-01

  The parent file `FermatTwoSquaresOQ04.lean` builds the arithmetic engine of
  Jacobi's two-square theorem: the divisor-character sum

        δ(n) := ∑_{d ∣ n} χ₄(d)    (`jacobiSum n`),

  proves it multiplicative, and establishes the *qualitative* shadow of Jacobi's
  theorem (δ(n) > 0 ⇔ n is a sum of two squares).  What the parent leaves open is
  the **exact value** of δ — it proves positivity and the prime-power geometric
  sums, but not the closed form.

  This file supplies the missing *quantitative* increment: the exact value of δ
  on every prime power and the resulting closed-form product

        δ(n) = ∏_{p ∣ n, p ≡ 1 (mod 4)} (vₚ(n) + 1)        (for representable n),

  which is precisely the count side of Jacobi's theorem `r₂(n) = 4·δ(n)`.  In
  words: the number of (ordered, signed) representations of `n` as a sum of two
  squares is four times the product of `(exponent + 1)` over the prime factors of
  `n` congruent to 1 mod 4 — provided every prime factor ≡ 3 (mod 4) occurs to an
  even power (otherwise the count is 0).

  Concretely the three prime-power values are

        δ(2^k) = 1,   δ(p^k) = k+1  (p ≡ 1),   δ(p^k) = [k even]  (p ≡ 3),

  and the closed form is their Dirichlet product via `isMultiplicative_jacobiSum`.
  We also give the divisor-counting form δ(n) = #{d∣n : d≡1} − #{d∣n : d≡3}.

  NOT proved here (and genuinely open in this gallery): the counting identity
  `r₂(n) = 4·δ(n)` itself.  Establishing it requires the arithmetic of the
  Gaussian integers ℤ[i] (unique factorization + a norm-counting bijection),
  which Mathlib does not yet provide.  This file is the exact-value half of the
  statement; the Gaussian-integer bijection remains the open half.

  References:
  - Jacobi (1834): r₂(n) = 4 ∑_{d∣n} χ₄(d)
  - FermatTwoSquaresOQ04.lean: parent — the divisor-character engine (δ multiplicative,
    prime-power geometric sums, δ>0 ⇔ representable)
  - Mathlib `neg_one_geom_sum`, `DirichletCharacter.χ₄`
-/

import Proofs.FermatTwoSquaresOQ04
import Mathlib.Tactic

open ArithmeticFunction DirichletCharacter ZMod Finset FermatTwoSquaresOQ04

namespace FermatTwoSquaresOQ04OQ01

-- ============================================================================
-- Part I: Exact prime-power values of δ
-- ============================================================================

/-- `δ(2^k) = 1`.  The character `χ₄` vanishes on even arguments, so only the
divisor `d = 1` contributes: the geometric sum `∑_{i≤k} 0^i` collapses to `1`. -/
theorem jacobiSum_two_pow (k : ℕ) : jacobiSum (2 ^ k) = 1 := by
  rw [jacobiSum_prime_pow Nat.prime_two]
  have h0 : χ₄ ((2 : ℕ) : ZMod 4) = 0 := by
    rw [χ₄_nat_eq_if_mod_four]; norm_num
  rw [h0, sum_range_succ']
  simp only [pow_succ, mul_zero, sum_const_zero, pow_zero, zero_add]

/-- `δ(p^k) = k + 1` for a prime `p ≡ 1 (mod 4)`.  Here `χ₄(p) = 1`, so the
geometric sum `∑_{i≤k} 1^i` counts the `k+1` divisors `1, p, …, p^k`, each of
which is `≡ 1 (mod 4)`. -/
theorem jacobiSum_prime_pow_one_mod_four {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (k : ℕ) : jacobiSum (p ^ k) = (k : ℤ) + 1 := by
  rw [jacobiSum_prime_pow hp, χ₄_nat_one_mod_four hmod]
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- `δ(p^k) = [k even]` for a prime `p ≡ 3 (mod 4)`: it is `1` when the exponent
is even and `0` when it is odd.  Here `χ₄(p) = -1`, so the alternating geometric
sum `∑_{i≤k} (-1)^i` telescopes to the parity indicator. -/
theorem jacobiSum_prime_pow_three_mod_four {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3)
    (k : ℕ) : jacobiSum (p ^ k) = if Even k then 1 else 0 := by
  rw [jacobiSum_prime_pow hp, χ₄_nat_three_mod_four hmod, neg_one_geom_sum]
  by_cases hk : Even k
  · rw [if_pos hk, if_neg (by rw [Nat.even_add_one]; simpa using hk)]
  · rw [if_neg hk, if_pos (by rw [Nat.even_add_one]; simpa using hk)]

-- ============================================================================
-- Part II: The closed-form product — Jacobi's exact count
-- ============================================================================

/-- **Jacobi's exact count (closed form).**  For a representable `n ≠ 0` — one in
which every prime factor `q ≡ 3 (mod 4)` occurs to an even power — the divisor-
character sum evaluates to the product of `(exponent + 1)` over the prime factors
`≡ 1 (mod 4)`:

      δ(n) = ∏_{p ∣ n, p ≡ 1 (mod 4)} (vₚ(n) + 1).

Combined with Jacobi's identity `r₂(n) = 4·δ(n)` (the open Gaussian-integer half),
this is the exact number of ordered signed representations of `n` as a sum of two
squares. -/
theorem jacobiSum_eq_prod_one_mod_four {n : ℕ} (hn : n ≠ 0)
    (hrep : ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (n.factorization q)) :
    jacobiSum n = ∏ p ∈ n.primeFactors with p % 4 = 1, ((n.factorization p : ℤ) + 1) := by
  have hprod : jacobiSum n
      = ∏ p ∈ n.primeFactors, jacobiSum (p ^ n.factorization p) := by
    rw [isMultiplicative_jacobiSum.multiplicative_factorization _ hn,
      ← Nat.support_factorization]
    rfl
  rw [hprod, prod_filter]
  refine prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  by_cases h2 : p % 2 = 0
  · -- p = 2 : the factor is 1, and the condition p ≡ 1 is false
    have hp2 : p = 2 := (Nat.Prime.even_iff hpp).mp (Nat.even_iff.mpr h2)
    subst hp2
    rw [jacobiSum_two_pow, if_neg (by norm_num)]
  · by_cases h1 : p % 4 = 1
    · -- p ≡ 1 (mod 4) : the factor is vₚ(n) + 1
      rw [jacobiSum_prime_pow_one_mod_four hpp h1, if_pos h1]
    · -- p ≡ 3 (mod 4) : even power (by hypothesis) so the factor is 1
      have h3 : p % 4 = 3 := by omega
      rw [jacobiSum_prime_pow_three_mod_four hpp h3, if_pos (hrep p hp h3), if_neg h1]

-- ============================================================================
-- Part III: Divisor-counting form
-- ============================================================================

/-- **Divisor-counting form.**  Splitting the character sum by the value of `χ₄`
gives δ(n) as a difference of divisor counts:

      δ(n) = #{d ∣ n : d ≡ 1 (mod 4)} − #{d ∣ n : d ≡ 3 (mod 4)}.

(Even divisors contribute `χ₄(d) = 0` and drop out.)  This is the raw form of
Jacobi's count before the multiplicative closed form of Part II. -/
theorem jacobiSum_eq_divisor_count {n : ℕ} (hn : n ≠ 0) :
    jacobiSum n
      = ((n.divisors.filter (· % 4 = 1)).card : ℤ)
        - ((n.divisors.filter (· % 4 = 3)).card : ℤ) := by
  rw [jacobiSum_apply hn]
  have key : ∀ d : ℕ, χ₄ ((d : ℕ) : ZMod 4)
      = (if d % 4 = 1 then (1 : ℤ) else 0) - (if d % 4 = 3 then 1 else 0) := by
    intro d
    rw [χ₄_nat_eq_if_mod_four]
    rcases Nat.even_or_odd d with he | ho
    · have h20 : d % 2 = 0 := Nat.even_iff.mp he
      have h1 : d % 4 ≠ 1 := by omega
      have h3 : d % 4 ≠ 3 := by omega
      simp [h20, h1, h3]
    · have h21 : d % 2 = 1 := Nat.odd_iff.mp ho
      have h2ne : ¬ (d % 2 = 0) := by omega
      rcases (by omega : d % 4 = 1 ∨ d % 4 = 3) with h1 | h3
      · simp [h2ne, h1]
      · simp [h2ne, h3]
  rw [sum_congr rfl (fun d _ => key d), sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]

-- ============================================================================
-- Part IV: Worked values (axiom-free)
-- ============================================================================

/-- `δ(25) = 3`  (so `r₂(25) = 12`): `25 = 5²`, `5 ≡ 1 (mod 4)`, exponent `2`. -/
example : jacobiSum (5 ^ 2) = 3 := by
  rw [jacobiSum_prime_pow_one_mod_four (p := 5) (by norm_num) (by norm_num) 2]; norm_num

/-- `δ(13³) = 4`  (so `r₂(2197) = 16`): `13 ≡ 1 (mod 4)`, exponent `3`. -/
example : jacobiSum (13 ^ 3) = 4 := by
  rw [jacobiSum_prime_pow_one_mod_four (p := 13) (by norm_num) (by norm_num) 3]; norm_num

/-- `δ(9) = 1`: `9 = 3²`, `3 ≡ 3 (mod 4)` to an even power ⇒ representable, count 1. -/
example : jacobiSum (3 ^ 2) = 1 := by
  rw [jacobiSum_prime_pow_three_mod_four (p := 3) (by norm_num) (by norm_num) 2, if_pos (by decide)]

/-- `δ(27) = 0`: `27 = 3³`, odd power of `3 ≡ 3 (mod 4)` ⇒ not a sum of two squares. -/
example : jacobiSum (3 ^ 3) = 0 := by
  rw [jacobiSum_prime_pow_three_mod_four (p := 3) (by norm_num) (by norm_num) 3, if_neg (by decide)]

/-- `δ(2^k) = 1` for every `k`: powers of two contribute nothing to the count. -/
example : jacobiSum (2 ^ 10) = 1 := jacobiSum_two_pow 10

end FermatTwoSquaresOQ04OQ01
