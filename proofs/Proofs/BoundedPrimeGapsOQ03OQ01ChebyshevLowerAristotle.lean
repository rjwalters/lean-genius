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

  PROGRESS (researcher-2): L1 (`log_factorial_eq_sum_vonMangoldt_mul_div`) and L3
  (`log_four_le_log_centralBinom`) are fully proved; L2 (`log_centralBinom_le_psi`) and
  the final assembly (`chebyshev_psi_lower_bound`) remain `sorry`. The L1 proof is written
  but UNVERIFIED — docker build infra is down (daemon unresponsive, fleet outage), so it
  has not been compiled. Verify before relying on it.

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
  -- Step 1: `N! = ∏_{n ∈ Ioc 0 N} n`, cast to ℝ.
  have hfact : (Nat.factorial N : ℝ) = ∏ n ∈ Finset.Ioc 0 N, (n : ℝ) := by
    have hnat : (∏ n ∈ Finset.Ioc 0 N, n) = Nat.factorial N := by
      have hI : Finset.Ioc 0 N = Finset.Ico 1 (N + 1) := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_Ico]
        omega
      rw [hI, Finset.prod_Ico_id_eq_factorial]
    rw [← hnat, Nat.cast_prod]
  rw [hfact]
  -- Step 2: `log ∏ = ∑ log` (each factor is positive on `Ioc 0 N`).
  rw [Real.log_prod (fun n hn => by
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    exact_mod_cast hn0.ne')]
  -- Step 3: replace `log n` by `∑_{d ∈ n.divisors} Λ d`.
  rw [Finset.sum_congr rfl (fun n _ => (ArithmeticFunction.vonMangoldt_sum).symm)]
  -- Step 4: rewrite each divisor-sum as a filtered sum over the common index `Ioc 0 N`.
  have step4 : ∀ n ∈ Finset.Ioc 0 N,
      (∑ d ∈ n.divisors, Λ d)
        = ∑ d ∈ Finset.Ioc 0 N, (if d ∣ n then Λ d else 0) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
    have hset : n.divisors = (Finset.Ioc 0 N).filter (fun d => d ∣ n) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨hdvd, -⟩
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn0
        have hd_le : d ≤ n := Nat.le_of_dvd hn0 hdvd
        exact ⟨⟨hd_pos, by omega⟩, hdvd⟩
      · rintro ⟨-, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl step4, Finset.sum_comm]
  -- Step 5: collapse the constant inner sum to `Λ d * (N / d)`.
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div,
    nsmul_eq_mul, mul_comm]

/-- **L2 — the genuine gap: `log C(2n,n) ≤ ψ(2n)`.**

Apply L1 with `N = 2n` and `N = n`:
`log C(2n,n) = log((2n)!) − 2·log(n!) = ∑_{d ∈ Ioc 0 2n} Λ d · (⌊2n/d⌋ − 2⌊n/d⌋)`
(the `n`-sum extends to `Ioc 0 2n` since `⌊n/d⌋ = 0` for `d > n`). Each bracket lies in
`{0,1}` (`0 ≤ ⌊2n/d⌋ − 2⌊n/d⌋ ≤ 1`) and `Λ d ≥ 0` (`vonMangoldt_nonneg`), so the sum is
`≤ ∑_{d ∈ Ioc 0 2n} Λ d = ψ(2n)`.

Lemma-level plan (Mathlib v4.26.0 hooks confirmed; complete when build infra recovers):
  • Factorial form of C(2n,n): `Nat.choose_mul_factorial_mul_factorial (le : n ≤ 2*n)` gives
    `(2n).choose n * n ! * (2n - n)! = (2n)!` with `2n - n = n`; combined with
    `Nat.centralBinom_eq_two_mul_choose` this yields, after `Nat.cast_*` to ℝ and
    `Real.log_div`/`Real.log_mul` (positivity from `Nat.factorial_pos`,
    `Nat.centralBinom_pos`), `log C(2n,n) = log((2n)!) − 2·log(n!)`.
  • Rewrite both factorials by `log_factorial_eq_sum_vonMangoldt_mul_div` (L1) at `N = 2n`
    and `N = n`. Extend the `N = n` sum from `Ioc 0 n` to `Ioc 0 2n` via
    `Finset.sum_subset` (`Ioc_subset_Ioc_right (by omega)`); the new terms vanish because
    `n / d = 0` for `d > n` (`Nat.div_eq_of_lt`).
  • Merge into `∑_{d ∈ Ioc 0 2n} Λ d * (↑(2n/d) − 2·↑(n/d))` and bound termwise by
    `Λ d * 1`: use `ArithmeticFunction.vonMangoldt_nonneg` together with the ℕ bracket
    bound `2n/d ≤ 2*(n/d) + 1` (proved: lower `Nat.mul_div_le_mul_div_assoc 2 n d`; upper
    via `Nat.div_lt_iff_lt_mul hd` reducing to `2n < (2*(n/d)+2)*d`, closed by
    `Nat.div_add_mod` + `nlinarith`/`ring`, NOT `omega` — the step is nonlinear in `d, n/d`).
  • `Chebyshev.psi (2 * n) = ∑ d ∈ Ioc 0 (2n), Λ d` by unfolding `Chebyshev.psi` and
    `Nat.floor_natCast` (note `(2 * n : ℝ)` casts as `↑(2*n)`), giving the final `≤`. -/
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
