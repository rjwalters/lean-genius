/-
# Euler's Odd-Perfect Form — the global assembly (`N = p^a · m²`)

This file completes **Euler's structural theorem (1747)** on odd perfect
numbers by assembling the local prime-power engine of `SumOfDivisorsOQ01.lean`
and the square-packaging half of `SumOfDivisorsOQ01SquarePacking.lean` into the
full conclusion:

> **Theorem (Euler).** If `N` is odd and perfect (`σ(N) = 2N`), then
> ```
>         N = p ^ a · m ²
> ```
> with `p` prime, `p ≡ 1 (mod 4)`, `a ≡ 1 (mod 4)`, and `¬ p ∣ m`.

This is a *conditional* structure theorem; it assumes nothing about whether any
odd perfect number exists (that question is open).

## Proof architecture (the two-factor mod-4 split)

The classical proof isolates the *special* (Euler) prime by a global `v₂`
count over the whole factorization.  We avoid the general "exactly one
odd-exponent prime" bookkeeping with a sharper **two-factor** argument that
localises the mod-4 analysis to a single coprime split:

1. **A special prime exists.**  `σ(N) = 2N` is even, so `N` is not a perfect
   square (`odd_perfect_not_isSquare`); by `isSquare_iff_even_factorization`
   some prime `p₀` divides `N` to an *odd* power `e := v_{p₀}(N)`.

2. **Split off its full prime power.**  Write `N = p₀^e · m` with
   `m = ordCompl[p₀] N`, coprime to `p₀` (`Nat.coprime_ordCompl`,
   `Nat.not_dvd_ordCompl`).  Multiplicativity of `σ` gives
   `σ(N) = σ(p₀^e) · σ(m)`.

3. **`σ(p₀^e)` is even** (L1, `sigma_prime_pow_odd_iff`, since `e` is odd) and
   `σ(N) ≡ 2 (mod 4)` (because `N` is odd).  Two even factors would force
   `4 ∣ σ(N)`; hence `σ(m)` is **odd**.

4. **`m` is a square** (`odd_sigma_odd_iff_isSquare`), say `m = r²` — the `m²`
   of Euler's form — and, `σ(m)` being odd, the mod-4 residue of `σ(N) = 2N`
   transfers entirely to the special factor: `σ(p₀^e) ≡ 2 (mod 4)`.

5. **The mod-4 refinement** (L2, `sigma_prime_pow_mod_four`) converts
   `σ(p₀^e) ≡ 2 (mod 4)` into `p₀ ≡ 1 (mod 4)` and `e ≡ 1 (mod 4)`.

Assembling: `N = p₀^e · r²` with `p₀ ≡ e ≡ 1 (mod 4)` and `¬ p₀ ∣ r`.
-/
import Mathlib
import Proofs.SumOfDivisorsOQ01
import Proofs.SumOfDivisorsOQ01SquarePacking

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace SumOfDivisorsOQ01

/-- **Euler's structural theorem for odd perfect numbers.**  If `N` is odd and
perfect, then `N = p ^ a · m ²` with `p` prime, `p ≡ 1 (mod 4)`,
`a ≡ 1 (mod 4)`, and `¬ p ∣ m` (so `gcd(p, m) = 1`).  The prime `p` is the
*special* (Euler) prime: it is the unique prime dividing `N` to an odd power,
and all other primes assemble into the square `m²`.

The statement is conditional: it does **not** assert that any odd perfect number
exists (open). -/
theorem odd_perfect_euler_form {N : ℕ} (hodd : Odd N) (hperf : Nat.Perfect N) :
    ∃ p a m : ℕ, p.Prime ∧ p % 4 = 1 ∧ a % 4 = 1 ∧ ¬ p ∣ m ∧ N = p ^ a * m ^ 2 := by
  have hN : N ≠ 0 := hperf.2.ne'
  -- σ(N) = 2N, and since N is odd, σ(N) ≡ 2 (mod 4).
  have hsig : sigma 1 N = 2 * N := odd_perfect_sigma_eq_two_mul hperf
  have hsig4 : sigma 1 N % 4 = 2 := by
    rw [hsig]; obtain ⟨k, hk⟩ := hodd; omega
  -- N is not a perfect square, so some prime has an odd exponent.
  have hnotsq : ¬ IsSquare N := odd_perfect_not_isSquare hodd hperf
  have hex : ∃ p, Odd (N.factorization p) := by
    by_contra h
    push_neg at h
    exact hnotsq ((isSquare_iff_even_factorization hN).mpr fun p =>
      Nat.not_odd_iff_even.mp (h p))
  obtain ⟨p₀, hp₀odd⟩ := hex
  -- p₀ is a prime factor (odd exponent ⇒ nonzero), and is itself odd.
  have hfpos : N.factorization p₀ ≠ 0 := by
    have h2 := Nat.odd_iff.mp hp₀odd; omega
  have hp₀mem : p₀ ∈ N.primeFactors := by
    rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hfpos
  have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀mem
  have hp₀oddprime : Odd p₀ := Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hp₀mem)
  -- Split off the full p₀-power: N = p₀^e · m, with m coprime to p₀.
  have hsplit : p₀ ^ N.factorization p₀ * ordCompl[p₀] N = N :=
    Nat.ordProj_mul_ordCompl_eq_self N p₀
  set e := N.factorization p₀ with he
  set m := ordCompl[p₀] N with hm
  have hcop1 : Nat.Coprime p₀ m := Nat.coprime_ordCompl hp₀prime hN
  have hcopE : Nat.Coprime (p₀ ^ e) m := hcop1.pow_left e
  have hmpos : 0 < m := Nat.ordCompl_pos p₀ hN
  have hmne : m ≠ 0 := hmpos.ne'
  have hmdvd : m ∣ N := Nat.ordCompl_dvd N p₀
  have hmodd : Odd m := Odd.of_dvd_nat hodd hmdvd
  have hpnotm : ¬ p₀ ∣ m := Nat.not_dvd_ordCompl hp₀prime hN
  -- Multiplicativity of σ across the coprime split.
  have hsigsplit : sigma 1 N = sigma 1 (p₀ ^ e) * sigma 1 m := by
    conv_lhs => rw [← hsplit]
    exact isMultiplicative_sigma.map_mul_of_coprime hcopE
  -- σ(p₀^e) is even because e is odd (L1).
  have hsigPeven : Even (sigma 1 (p₀ ^ e)) := by
    rw [← Nat.not_odd_iff_even, sigma_prime_pow_odd_iff hp₀prime hp₀oddprime]
    exact Nat.not_even_iff_odd.mpr hp₀odd
  -- Two even factors would give 4 ∣ σ(N); since σ(N) ≡ 2 (mod 4), σ(m) is odd.
  have hsigModd : Odd (sigma 1 m) := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    obtain ⟨u, hu⟩ := hsigPeven
    obtain ⟨v, hv⟩ := h
    rw [hsigsplit, hu, hv] at hsig4
    have hexp : (u + u) * (v + v) = 4 * (u * v) := by ring
    rw [hexp] at hsig4
    omega
  -- σ(m) odd ⇒ m is a perfect square (square-packaging half).
  obtain ⟨r, hr⟩ := (odd_sigma_odd_iff_isSquare hmodd hmne).mp hsigModd
  -- σ(m) being odd, the mod-4 residue of σ(N) = 2N lands on the special factor.
  have hsigP4 : sigma 1 (p₀ ^ e) % 4 = 2 := by
    obtain ⟨u, hu⟩ := hsigPeven
    obtain ⟨w, hw⟩ := hsigModd
    rw [hsigsplit, hu, hw] at hsig4
    have hexp : (u + u) * (2 * w + 1) = 4 * (u * w) + 2 * u := by ring
    rw [hexp] at hsig4
    rw [hu]; omega
  -- L2: σ(p₀^e) ≡ 2 (mod 4) ⇒ p₀ ≡ 1 and e ≡ 1 (mod 4).
  obtain ⟨hp4, he4⟩ :=
    (sigma_prime_pow_mod_four hp₀prime hp₀oddprime hp₀odd).mp hsigP4
  -- Assemble Euler's form.
  refine ⟨p₀, e, r, hp₀prime, hp4, he4, ?_, ?_⟩
  · intro hdvd
    apply hpnotm
    rw [hr]
    exact hdvd.mul_right r
  · rw [← hsplit, hr]; ring

end SumOfDivisorsOQ01
