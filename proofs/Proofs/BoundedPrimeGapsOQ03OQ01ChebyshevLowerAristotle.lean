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

  PROGRESS (researcher-2): ALL FOUR obligations are now proved — L1
  (`log_factorial_eq_sum_vonMangoldt_mul_div`), L2 (`log_centralBinom_le_psi`),
  L3 (`log_four_le_log_centralBinom`) and the final real-analysis assembly
  (`chebyshev_psi_lower_bound`, with explicit constant `c = (log 2)/4`). The file is
  now `sorry`-free. The proofs are written but UNVERIFIED — docker build infra is down
  (daemon unresponsive, mem=0; Aristotle backend 404), so they have not been compiled.
  Verify before relying on them. The L2 derivation is the genuine combinatorial gap:
  `log C(2n,n) = log(2n)! − 2·log n! = ∑_{d≤2n} Λ d·(⌊2n/d⌋ − 2⌊n/d⌋) ≤ ∑_{d≤2n} Λ d = ψ(2n)`,
  with each de Polignac bracket `⌊2n/d⌋ − 2⌊n/d⌋ ∈ {0,1}` and `Λ d ≥ 0`.

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
  -- Positivity facts.
  have hfn : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hcbpos : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  -- Step 1: `log C(2n,n) = log (2n)! − 2·log n!`, from
  -- `C(2n,n) · n! · n! = (2n)!` (`choose_mul_factorial_mul_factorial`).
  have hcb_def : Nat.centralBinom n = (2 * n).choose n := rfl
  have hkey : (Nat.centralBinom n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)
      = (Nat.factorial (2 * n) : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    have h2 : 2 * n - n = n := by omega
    rw [h2] at h
    rw [hcb_def]
    exact_mod_cast h
  have hlogkey : Real.log (Nat.centralBinom n : ℝ)
      = Real.log (Nat.factorial (2 * n) : ℝ) - 2 * Real.log (Nat.factorial n : ℝ) := by
    have hl := congrArg Real.log hkey
    rw [Real.log_mul (ne_of_gt (mul_pos hcbpos hfn)) (ne_of_gt hfn),
        Real.log_mul (ne_of_gt hcbpos) (ne_of_gt hfn)] at hl
    linarith
  rw [hlogkey, log_factorial_eq_sum_vonMangoldt_mul_div (2 * n),
      log_factorial_eq_sum_vonMangoldt_mul_div n]
  -- Step 2: extend the `N = n` sum from `Ioc 0 n` to `Ioc 0 (2n)`; the new
  -- terms vanish since `n / d = 0` whenever `d > n`.
  have hext : (∑ d ∈ Finset.Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ))
      = ∑ d ∈ Finset.Ioc 0 (2 * n), Λ d * ((n / d : ℕ) : ℝ) := by
    apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right (by omega))
    intro d hd hdnotin
    have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hdn : n < d := by
      rcases Nat.lt_or_ge n d with h | h
      · exact h
      · exact absurd (Finset.mem_Ioc.mpr ⟨hd0, h⟩) hdnotin
    rw [Nat.div_eq_of_lt hdn]
    simp
  rw [hext, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- Step 3: `ψ(2n) = ∑_{d ∈ Ioc 0 2n} Λ d` (unfold `psi`, evaluate the floor).
  have hfloor : ⌊(2 : ℝ) * (n : ℝ)⌋₊ = 2 * n := by
    rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hpsi : Chebyshev.psi (2 * (n : ℝ)) = ∑ d ∈ Finset.Ioc 0 (2 * n), Λ d := by
    unfold Chebyshev.psi
    rw [hfloor]
  -- ℕ bracket bound: `⌊2n/d⌋ ≤ 2⌊n/d⌋ + 1` (nonlinear in `d`, `n/d`).
  have hbracket : ∀ d : ℕ, 2 * n / d ≤ 2 * (n / d) + 1 := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hd, Nat.succ_eq_add_one]
      have h1 := Nat.div_add_mod n d
      have h2 := Nat.mod_lt n hd
      nlinarith [h1, h2]
  rw [hpsi]
  -- Step 4: termwise, `Λ d · (⌊2n/d⌋ − 2⌊n/d⌋) ≤ Λ d · 1 = Λ d` since `Λ d ≥ 0`.
  apply Finset.sum_le_sum
  intro d _
  have hLnn : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  have hbr : ((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ) ≤ 1 := by
    have hc : ((2 * n / d : ℕ) : ℝ) ≤ 2 * ((n / d : ℕ) : ℝ) + 1 := by exact_mod_cast hbracket d
    linarith
  have hfactor : Λ d * ((2 * n / d : ℕ) : ℝ) - 2 * (Λ d * ((n / d : ℕ) : ℝ))
      = Λ d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) := by ring
  rw [hfactor]
  calc Λ d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ))
      ≤ Λ d * 1 := mul_le_mul_of_nonneg_left hbr hLnn
    _ = Λ d := mul_one _

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

/-- **Assembly — the missing ingredient.** A Chebyshev-strength lower bound on `ψ`,
with the explicit constant `c = (log 2)/4`.

Combine L3 then L2 to get `ψ(2n) ≥ n·log 4 − log(2n)`. The elementary estimate
`2n ≤ 2ⁿ` (hence `log(2n) ≤ n·log 2`) collapses the right side to
`n·log 4 − n·log 2 = n·log 2`, so `ψ(2n) ≥ n·log 2` for every `n ≥ 1` — no asymptotics
needed. For real `x ≥ 2` put `n = ⌊x/2⌋ ≥ 1`; then `2n ≤ x` (so `ψ(2n) ≤ ψ x` by
`Chebyshev.psi_mono`) and `n ≥ x/4` (a single linear combination of `n ≥ 1` and
`x/2 < n + 1`), giving `(log 2 / 4)·x = log 2·(x/4) ≤ n·log 2 ≤ ψ(2n) ≤ ψ x`. -/
theorem chebyshev_psi_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * x ≤ Chebyshev.psi x := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Self-contained: `2m ≤ 2^m` for `m ≥ 1`.
  have h2npow : ∀ m : ℕ, 1 ≤ m → 2 * m ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; decide
      · have hih := ih hkpos
        rw [pow_succ]
        nlinarith [hih, hkpos]
  -- The combined integer bound: `ψ(2n) ≥ n·log 2` for `n ≥ 1`.
  have key : ∀ n : ℕ, 0 < n → (n : ℝ) * Real.log 2 ≤ Chebyshev.psi (2 * n) := by
    intro n hn
    have hL2 := log_centralBinom_le_psi n
    have hL3 := log_four_le_log_centralBinom n hn
    -- `log(2n) ≤ n·log 2`, from `2n ≤ 2^n`.
    have hcast : ((2 * n : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
      calc ((2 * n : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h2npow n hn
        _ = (2 : ℝ) ^ n := by push_cast; ring
    have h2npos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * n by omega)
    have hlog2n : Real.log (2 * (n : ℝ)) ≤ (n : ℝ) * Real.log 2 := by
      have h1 : Real.log ((2 * n : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ n) :=
        Real.log_le_log h2npos hcast
      rw [Real.log_pow] at h1
      have hcast2 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
      rw [hcast2] at h1
      linarith
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hlog4n : (n : ℝ) * Real.log 4 = 2 * ((n : ℝ) * Real.log 2) := by
      rw [hlog4]; ring
    linarith [hL2, hL3, hlog2n, hlog4n]
  refine ⟨Real.log 2 / 4, by linarith, ?_⟩
  intro x hx
  set n := ⌊x / 2⌋₊ with hn_def
  have hxhalf : (0 : ℝ) ≤ x / 2 := by linarith
  have hn1 : 1 ≤ n := by
    rw [hn_def]; apply Nat.le_floor; push_cast; linarith
  have hnpos : 0 < n := hn1
  have hfloor_le : (n : ℝ) ≤ x / 2 := by rw [hn_def]; exact Nat.floor_le hxhalf
  have h2nx : 2 * (n : ℝ) ≤ x := by linarith
  have hlt_floor : x / 2 < (n : ℝ) + 1 := by
    rw [hn_def]; exact Nat.lt_floor_add_one (x / 2)
  have hn_ge_1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hge : x / 4 ≤ (n : ℝ) := by linarith
  have hk := key n hnpos
  have hpsi_mono : Chebyshev.psi (2 * (n : ℝ)) ≤ Chebyshev.psi x := Chebyshev.psi_mono h2nx
  calc Real.log 2 / 4 * x = Real.log 2 * (x / 4) := by ring
    _ ≤ Real.log 2 * (n : ℝ) := mul_le_mul_of_nonneg_left hge (le_of_lt hlog2pos)
    _ = (n : ℝ) * Real.log 2 := by ring
    _ ≤ Chebyshev.psi (2 * (n : ℝ)) := hk
    _ ≤ Chebyshev.psi x := hpsi_mono

end BoundedPrimeGapsOQ03OQ01.ChebyshevLowerDecomp
