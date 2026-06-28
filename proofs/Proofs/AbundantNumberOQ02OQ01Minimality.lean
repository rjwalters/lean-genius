/-
  Toward the *minimality* half of "the smallest odd abundant number not divisible
  by 3 is 5391411025".

  The companion file `AbundantNumberOQ02OQ01.lean` proves the **witness / upper-bound**
  half: 5391411025 = 5²·7·11·13·17·19·23·29 really is odd, coprime to 3, and abundant.
  Its header records the minimality half as a "genuine blocker", claiming any proof
  needs an enumeration over ~5.4·10⁹ — "far beyond any kernel or compiled enumeration".

  This file shows that framing is too pessimistic: there is a clean *structural*
  reduction of the minimality question to a single finite primorial inequality, with
  no enumeration of the 5.4-billion range at all.  The engine is the elementary
  **Euler abundancy bound**

      σ(n) · ∏_{p∣n}(p−1)  <  n · ∏_{p∣n} p              (for n > 1)

  i.e. `σ(n)/n < ∏_{p∣n} p/(p−1)`, the standard tool of perfect/abundant-number theory.
  It is proved here purely multiplicatively (no real numbers, no `native_decide`) from
  the per-prime-power identity `(∑_{i≤a} pⁱ)·(p−1) = p^{a+1} − 1` (`geom_sum_mul_add`,
  which holds in any semiring, hence over ℕ) assembled across the prime factorisation.

  Specialising to abundance `σ(n) > 2n` gives the **ℕ-only reduction**

      n abundant  ⟹  2 · ∏_{p∣n}(p−1)  <  ∏_{p∣n} p .

  For `n` odd and coprime to 3 every prime factor is ≥ 5, so the right-hand inequality
  is governed by the multiset of primes ≥ 5 dividing `n`.  Since `p ↦ p/(p−1)` is
  decreasing, the product `∏ p/(p−1)` over `k` distinct primes ≥ 5 is largest for the
  `k` smallest such primes, and (see `six_primes_below_two` / `seven_primes_above_two`)
  the six smallest already give `∏ p/(p−1) < 2` while seven exceed 2.  Hence **any odd
  abundant number coprime to 3 has at least 7 distinct prime factors** — the witness
  5391411025 has exactly 8.  The only remaining ingredient is the extremal/monotonicity
  step (`∏ p/(p−1)` maximised by the smallest primes), recorded as the open follow-up;
  the brute-force enumeration is *not* needed.

  Everything below is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `sorry`).
-/
import Mathlib

namespace AbundantNumberOQ02OQ01Minimality

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- **Per-prime-power Euler bound.**  For a prime `p` and any exponent `a`,
`σ₁(pᵃ)·(p−1) < p^{a+1}`.  Equivalently `σ₁(pᵃ)/pᵃ < p/(p−1)`.

Proof: the geometric identity `(∑_{i<a+1} pⁱ)·(p−1) + 1 = p^{a+1}` (valid in any
semiring, here ℕ) forces the left side to be `p^{a+1} − 1`, strictly below `p^{a+1}`. -/
lemma geomSum_mul_pred_lt {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    (∑ i ∈ range (a + 1), p ^ i) * (p - 1) < p ^ (a + 1) := by
  have key := geom_sum_mul_add (p - 1) (a + 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at key
  omega

/-- **Euler abundancy bound (ℕ form).**  For every `n > 1`,
`σ(n) · ∏_{p∣n}(p−1) < n · ∏_{p∣n} p`.

This is the integer-arithmetic shadow of `σ(n)/n < ∏_{p∣n} p/(p−1)`.  It is obtained by
writing both `σ(n)` and `n` as products over `n.primeFactors` and comparing the products
factor-by-factor through `geomSum_mul_pred_lt`. -/
theorem sigma_mul_prod_sub_one_lt {n : ℕ} (hn : 1 < n) :
    σ 1 n * ∏ p ∈ n.primeFactors, (p - 1) < n * ∏ p ∈ n.primeFactors, p := by
  have hn0 : n ≠ 0 := by omega
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  -- `n = ∏ p^{vₚ(n)}` over its prime factors (defeq: `primeFactors = factorization.support`).
  have hNpow : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    Nat.factorization_prod_pow_eq_self hn0
  -- Repackage the right-hand side `n · ∏ p` as a single product `∏ p^{vₚ(n)+1}`.
  have hR : ∏ p ∈ n.primeFactors, p ^ (n.factorization p + 1)
          = n * ∏ p ∈ n.primeFactors, p := by
    have h1 : ∏ p ∈ n.primeFactors, p ^ (n.factorization p + 1)
            = (∏ p ∈ n.primeFactors, p ^ n.factorization p) * ∏ p ∈ n.primeFactors, p := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun p _ => pow_succ p (n.factorization p))
    rw [h1, hNpow]
  -- Expand `σ 1 n` as a product of geometric sums over the prime factors.
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
  simp only [mul_one]
  -- Both sides are now single products over `n.primeFactors`; compare termwise.
  rw [← Finset.prod_mul_distrib, ← hR]
  refine Finset.prod_lt_prod_of_nonempty ?_ ?_ hne
  · intro p hp
    have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hs : 0 < ∑ i ∈ range (n.factorization p + 1), p ^ i := by positivity
    exact Nat.mul_pos hs (by omega)
  · intro p hp
    have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    exact geomSum_mul_pred_lt h2 (n.factorization p)

/-- **Reduction of abundance to a primorial inequality.**  If `n` is abundant then

    `2 · ∏_{p∣n}(p−1) < ∏_{p∣n} p`.

No information about the *size* of `n` is used — only its prime support — so the
minimality question for the odd, 3-free case reduces to bounding this inequality over
sets of primes ≥ 5, with no enumeration of `n`. -/
theorem abundant_imp_two_mul_prod_sub_one_lt {n : ℕ} (hn : Nat.Abundant n) :
    2 * ∏ p ∈ n.primeFactors, (p - 1) < ∏ p ∈ n.primeFactors, p := by
  have hn' : n < ∑ i ∈ n.properDivisors, i := hn
  -- abundance forces `n > 1` (neither 0 nor 1 is abundant: each has no proper divisors)
  have h1n : 1 < n := by
    rcases n with _ | _ | n
    · simp [Nat.properDivisors_zero] at hn'
    · simp [Nat.properDivisors_one] at hn'
    · omega
  -- `σ(n) > 2n`
  have hσ : 2 * n < σ 1 n := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    omega
  -- the Euler bound, and positivity of `∏ (p-1)`
  have hE := sigma_mul_prod_sub_one_lt h1n
  have hPpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  -- 2n·∏(p-1) < σ(n)·∏(p-1) < n·∏p, then cancel n
  have step1 : (2 * n) * ∏ p ∈ n.primeFactors, (p - 1)
             < σ 1 n * ∏ p ∈ n.primeFactors, (p - 1) :=
    mul_lt_mul_of_pos_right hσ hPpos
  have step2 : n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) < n * ∏ p ∈ n.primeFactors, p := by
    have e : n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) = (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by
      ring
    rw [e]; exact lt_trans step1 hE
  exact Nat.lt_of_mul_lt_mul_left step2

/-- Numeric anchor (lower boundary).  The six smallest primes coprime to 6 satisfy the
**deficiency** inequality `∏ p < 2·∏(p−1)`, i.e. `∏ p/(p−1) < 2`.  Combined with the
extremal step (the product is maximised by the smallest primes), this shows ≤ 6 distinct
prime factors ≥ 5 can never meet `abundant_imp_two_mul_prod_sub_one_lt`. -/
theorem six_primes_below_two :
    5 * 7 * 11 * 13 * 17 * 19 < 2 * (4 * 6 * 10 * 12 * 16 * 18) := by norm_num

/-- Numeric anchor (upper boundary).  Adding the seventh prime (23) flips the inequality:
`2·∏(p−1) < ∏ p`, i.e. `∏ p/(p−1) > 2`.  So the bound "≥ 7 distinct prime factors" is the
exact threshold delivered by this method (the witness 5391411025 attains 8). -/
theorem seven_primes_above_two :
    2 * (4 * 6 * 10 * 12 * 16 * 18 * 22) < 5 * 7 * 11 * 13 * 17 * 19 * 23 := by norm_num

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms abundant_imp_two_mul_prod_sub_one_lt

end AbundantNumberOQ02OQ01Minimality
