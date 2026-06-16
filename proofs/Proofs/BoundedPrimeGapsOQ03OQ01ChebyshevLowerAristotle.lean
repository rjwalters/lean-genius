/-
  Chebyshev lower bound — DECOMPOSED Aristotle target for
  `bounded-prime-gaps-oq-03-oq-01-oq-01`.

  Companion to `BoundedPrimeGapsOQ03OQ01ChebyshevLower.lean`. That file states the
  monolithic missing ingredient

      chebyshev_psi_lower_bound : ∃ c, 0 < c ∧ ∀ x ≥ 2, c * x ≤ Chebyshev.psi x

  as a single `sorry`. This file breaks the classical de Polignac / central-binomial
  derivation into three named lemmas (L1–L3) plus the real-analysis assembly, so each
  obligation is an independent, tractable target for `prove_file`.

  STATUS: build-gated ORPHAN (not imported by Proofs.lean). Do NOT register until it
  compiles green with all sorries discharged.

  Confirmed Mathlib v4.26.0 hooks (verified by grep of the source tree this session):
    • `ArithmeticFunction.vonMangoldt_sum : ∑ i ∈ n.divisors, Λ i = Real.log n`
        (NumberTheory/ArithmeticFunction/VonMangoldt.lean:102)
    • `ArithmeticFunction.vonMangoldt_nonneg : 0 ≤ Λ n`  (same file:80)
    • `Nat.Ioc_filter_dvd_card_eq_div (n p : ℕ) : #{x ∈ Ioc 0 n | p ∣ x} = n / p`
        (Data/Nat/Factorization/Basic.lean:475) — note Ioc 0 N matches psi's own range.
    • `Nat.four_pow_le_two_mul_self_mul_centralBinom : ∀ n, 0 < n → 4^n ≤ 2*n * centralBinom n`
        (Data/Nat/Choose/Central.lean:99)
    • `Chebyshev.psi x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n`  (NumberTheory/Chebyshev.lean:55)
-/
import Mathlib

open scoped ArithmeticFunction
open Finset

namespace BoundedPrimeGapsOQ03OQ01.ChebyshevLowerDecomp

/-- **L1 — de Polignac / Legendre floor-sum identity.**
`log(N!) = ∑_{d ∈ Ioc 0 N} Λ d · ⌊N/d⌋`.

Derivation: `log(N!) = ∑_{n ∈ Ioc 0 N} log n = ∑_n ∑_{d ∈ n.divisors} Λ d`
(`vonMangoldt_sum`); swap the order of summation to `∑_{d ∈ Ioc 0 N} Λ d · #{n ∈ Ioc 0 N : d ∣ n}`,
then `Nat.Ioc_filter_dvd_card_eq_div` rewrites the inner count as `N / d`. -/
theorem log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (Nat.factorial N : ℝ) = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  sorry

/-- **L2 — the genuine gap: `log C(2n,n) ≤ ψ(2n)`.**

Apply L1 with `N = 2n` and `N = n`:
`log C(2n,n) = log((2n)!) − 2·log(n!) = ∑_{d ∈ Ioc 0 2n} Λ d · (⌊2n/d⌋ − 2⌊n/d⌋)`
(the `n`-sum extends to `Ioc 0 2n` since `⌊n/d⌋ = 0` for `d > n`). Each bracket lies in
`{0,1}` (`0 ≤ ⌊2n/d⌋ − 2⌊n/d⌋ ≤ 1`) and `Λ d ≥ 0` (`vonMangoldt_nonneg`), so the sum is
`≤ ∑_{d ∈ Ioc 0 2n} Λ d = ψ(2n)`. -/
theorem log_centralBinom_le_psi (n : ℕ) :
    Real.log (Nat.centralBinom n : ℝ) ≤ Chebyshev.psi (2 * n) := by
  sorry

/-- **L3 — central-binomial size bound: `n·log 4 − log(2n) ≤ log C(2n,n)`.**

Logarithm of `Nat.four_pow_le_two_mul_self_mul_centralBinom` (`4^n ≤ 2n · C(2n,n)`):
`n·log 4 = log(4^n) ≤ log(2n) + log C(2n,n)`. -/
theorem log_four_le_log_centralBinom (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * n) ≤ Real.log (Nat.centralBinom n : ℝ) := by
  have hbound : (4 : ℝ) ^ n ≤ 2 * (n : ℝ) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hcb : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have hlog : Real.log ((4 : ℝ) ^ n) ≤ Real.log (2 * (n : ℝ) * (Nat.centralBinom n : ℝ)) :=
    Real.log_le_log (by positivity) hbound
  rw [Real.log_pow, Real.log_mul (ne_of_gt h2n) (ne_of_gt hcb)] at hlog
  linarith

/-- **Assembly — the missing ingredient.** A Chebyshev-strength lower bound on `ψ`.

From L2 ∘ L3: `ψ(2n) ≥ n·log 4 − log(2n)`. Since `log(2n) = o(n)`, for a small positive
constant `c` (e.g. `c = (log 4)/4`) we get `c·(2n) ≤ ψ(2n)` for all `n ≥ 1`; monotonicity
of `ψ` (`Chebyshev.psi_mono`) plus `ψ x ≥ ψ(2⌊x/2⌋)` lifts this to every real `x ≥ 2`. -/
theorem chebyshev_psi_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * x ≤ Chebyshev.psi x := by
  sorry

end BoundedPrimeGapsOQ03OQ01.ChebyshevLowerDecomp
