import Mathlib

/-
# The Explicit Carmichael Function on the Prime-Power Factorization

## Open question (euler-totient-oq-01-oq-01-oq-01)

Parent `euler-totient-oq-01-oq-01` proves the keystone multiplicativity
λ(m·n) = lcm(λ(m), λ(n)) for coprime m, n, and asks to "complete the induction
over the prime-power factorization to state λ(n) = lcm_i λ(pᵢ^kᵢ) as a single
theorem".

## Honesty note — what is and isn't new here

The literal factorization identity is **already in Mathlib** as
`ArithmeticFunction.carmichael_factorization`:

    Carmichael n = n.primeFactors.lcm (fun p ↦ Carmichael (p ^ n.factorization p))

together with the per-prime-power closed forms
`carmichael_pow_of_prime_ne_two` (λ(p^k) = φ(p^k) for odd p) and
`carmichael_two_pow_of_ne_two` (λ(2^k) = 2^{k-2}, k ≠ 2).  Re-deriving any of
these would be a thin wrapper, so this file does **not** reprove them — it
*cites* them and contributes the parts Mathlib leaves unassembled:

1. The **explicit closed form** for odd n:
       λ(n) = lcm_{p | n} p^{k_p - 1}·(p - 1),
   obtained by collapsing each odd prime-power factor λ(p^{k}) = φ(p^{k})
   to its textbook value p^{k-1}(p-1).  Mathlib has the factorization lemma
   and the per-factor totient value separately; the single assembled formula
   is not stated there.

2. **Concrete evaluations** that are genuinely absent from Mathlib, including
   the first Carmichael number 561 = 3·11·17:
       λ(561) = lcm(2, 10, 16) = 80,  and  80 ∣ 560,
   the Korselt-style divisibility λ(561) ∣ (561 − 1) that makes 561 a
   Carmichael number.

`Carmichael` is Mathlib's reduced totient (the exponent of (ℤ/nℤ)ˣ), the same
function the parent file defines locally as `Monoid.exponent (ZMod n)ˣ`.
-/

open Nat ArithmeticFunction

namespace EulerTotientOQ01OQ01OQ01

/-! ## Explicit values on odd prime powers -/

/-- For an odd prime `p`, the Carmichael value is `λ(p) = p - 1` (the unit group
`(ℤ/pℤ)ˣ` is cyclic of order `p − 1`).  Specialises Mathlib's
`carmichael_pow_of_prime_ne_two` at exponent 1. -/
theorem carmichael_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Carmichael p = p - 1 := by
  have h := carmichael_pow_of_prime_ne_two 1 hp hp2
  rwa [pow_one, Nat.totient_prime hp] at h

/-- For an odd prime `p` and `k ≥ 1`, the Carmichael value has the textbook
closed form `λ(p^k) = p^{k-1}·(p-1) = φ(p^k)`.  Combines Mathlib's
`carmichael_pow_of_prime_ne_two` with `Nat.totient_prime_pow`. -/
theorem carmichael_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 0 < k) : Carmichael (p ^ k) = p ^ (k - 1) * (p - 1) := by
  rw [carmichael_pow_of_prime_ne_two k hp hp2, Nat.totient_prime_pow hp hk]

/-! ## The explicit closed form for odd `n` -/

/-- **Explicit Carmichael formula for odd `n`.**

For odd `n ≠ 0` with prime factorisation `n = ∏ p^{k_p}` (every `p` odd),

    λ(n) = lcm_{p ∈ primeFactors n} p^{k_p - 1}·(p - 1).

This is the assembled textbook formula: Mathlib's `carmichael_factorization`
reduces `λ(n)` to the lcm of the per-prime-power values `λ(p^{k_p})`, and each
of those collapses to `p^{k_p-1}(p-1)` because every prime factor of an odd
number is itself odd. -/
theorem carmichael_odd_eq_lcm_explicit {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    Carmichael n
      = n.primeFactors.lcm (fun p => p ^ (n.factorization p - 1) * (p - 1)) := by
  haveI : NeZero n := ⟨hn⟩
  rw [carmichael_factorization n]
  refine Finset.lcm_congr rfl (fun p hp => ?_)
  have hpp : p.Prime := prime_of_mem_primeFactors hp
  have hdvd : p ∣ n := dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hk : 0 < n.factorization p := hpp.factorization_pos_of_dvd hn hdvd
  rw [carmichael_odd_prime_pow hpp hp2 hk]

/-! ## Euler's theorem, sharpened

The universal-exponent property and the divisibility `λ(n) ∣ φ(n)` are exactly
the content of Mathlib's `pow_carmichael` and `carmichael_dvd_totient`; we record
them here as the headline corollaries that motivate the Carmichael function. -/

/-- The universal exponent property (Mathlib `pow_carmichael`): every unit of
`ℤ/nℤ` is killed by `λ(n)`, i.e. `a^{λ(n)} = 1`.  This is the sharp form of
Euler's theorem `a^{φ(n)} ≡ 1`. -/
theorem pow_carmichael_eq_one {n : ℕ} (a : (ZMod n)ˣ) :
    a ^ Carmichael n = 1 := pow_carmichael a

/-- `λ(n) ∣ φ(n)` (Mathlib `carmichael_dvd_totient`): the Carmichael exponent
divides Euler's totient, so `λ(n)` is never larger than `φ(n)` and refines it. -/
theorem carmichael_dvd_totient' (n : ℕ) : Carmichael n ∣ n.totient :=
  carmichael_dvd_totient n

/-! ## Concrete evaluations

These specific values are not in Mathlib.  They exercise the multiplicative law
on genuinely distinct primes. -/

/-- `λ(15) = lcm(λ(3), λ(5)) = lcm(2, 4) = 4`. -/
theorem carmichael_15 : Carmichael 15 = 4 := by
  rw [show (15 : ℕ) = 3 * 5 from rfl, carmichael_mul (by decide),
      carmichael_odd_prime (p := 3) (by norm_num) (by norm_num),
      carmichael_odd_prime (p := 5) (by norm_num) (by norm_num)]
  decide

/-- **The first Carmichael number.** `561 = 3 · 11 · 17`, and
`λ(561) = lcm(λ(3), λ(11), λ(17)) = lcm(2, 10, 16) = 80`. -/
theorem carmichael_561 : Carmichael 561 = 80 := by
  rw [show (561 : ℕ) = 3 * (11 * 17) from rfl,
      carmichael_mul (by decide), carmichael_mul (by decide),
      carmichael_odd_prime (p := 3) (by norm_num) (by norm_num),
      carmichael_odd_prime (p := 11) (by norm_num) (by norm_num),
      carmichael_odd_prime (p := 17) (by norm_num) (by norm_num)]
  decide

/-- **Korselt's criterion witness for 561.** Since `λ(561) = 80` divides
`561 − 1 = 560`, every `a` coprime to 561 satisfies `a^{560} ≡ 1 (mod 561)`,
which is exactly why 561 is a Carmichael (Fermat-pseudoprime-to-every-base)
number. -/
theorem carmichael_561_dvd_560 : Carmichael 561 ∣ 560 := by
  rw [carmichael_561]; decide

end EulerTotientOQ01OQ01OQ01
