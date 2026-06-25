import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-
# Elementary PNT: the fundamental von Mangoldt summatory identity

This file formalises the exact identity at the heart of the *elementary* approach to the
Prime Number Theorem (the route of Chebyshev, Mertens, and ultimately Selberg–Erdős):

$$\sum_{m=1}^{N} \Lambda(m)\left\lfloor \frac{N}{m}\right\rfloor = \log(N!).$$

Here `Λ` is the von Mangoldt function (`Λ(p^k) = log p`, and `0` otherwise) and the floor
`⌊N/m⌋` is ordinary natural-number division.

## Why this is the cornerstone of elementary PNT

Every elementary proof of the Prime Number Theorem begins by estimating `log(N!)` in two ways:

* **Analytically**, via Stirling's formula: `log(N!) = N log N - N + O(log N)`.
* **Arithmetically**, via the divisor identity `log n = ∑_{d ∣ n} Λ(d)`, which on summing over
  `n ≤ N` and exchanging the order of summation produces exactly the floor-weighted sum
  formalised here.

Equating the two yields `∑_{m ≤ N} Λ(m) ⌊N/m⌋ = N log N - N + O(log N)`, the first
*error-bounded* statement on the road to `ψ(x) ∼ x`. This file supplies the arithmetic
identity in fully verified, axiom-free form, together with the immediate upper estimate
`log(N!) ≤ N · ∑_{m ≤ N} Λ(m)/m` obtained from `⌊N/m⌋ ≤ N/m`.

## Main results

* `PrimeNumberTheoremOQ03.log_factorial_eq_sum_log` —
  `log(N!) = ∑_{n=1}^{N} log n`.
* `PrimeNumberTheoremOQ03.vonMangoldt_summatory` —
  `∑_{m=1}^{N} Λ(m) ⌊N/m⌋ = log(N!)`.
* `PrimeNumberTheoremOQ03.log_factorial_le` —
  `log(N!) ≤ N · ∑_{m=1}^{N} Λ(m)/m`.

## Mathlib dependencies

The arithmetic input is `ArithmeticFunction.vonMangoldt_sum` (`∑_{d ∣ n} Λ(d) = log n`).
The counting input is `Nat.Ioc_filter_dvd_card_eq_div` (`#{x ∈ (0,N] : m ∣ x} = N/m`).
The order-exchange is `Finset.sum_comm'`. None of these supply the floor-weighted identity,
which is new here and absent from `Mathlib.NumberTheory.Chebyshev`.
-/

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction

namespace PrimeNumberTheoremOQ03

/-- `log(N!)` expands as the sum of `log n` for `n = 1, …, N`. -/
theorem log_factorial_eq_sum_log (N : ℕ) :
    Real.log ((Nat.factorial N : ℕ) : ℝ) = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
  have hprod : ∏ n ∈ Finset.Icc 1 N, (n : ℝ) = ((Nat.factorial N : ℕ) : ℝ) := by
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
      push_cast; ring
  rw [← hprod, Real.log_prod]
  intro n hn
  rw [Finset.mem_Icc] at hn
  exact Nat.cast_ne_zero.mpr (by omega)

/-- **Fundamental von Mangoldt summatory identity.**

`∑_{m=1}^{N} Λ(m) ⌊N/m⌋ = log(N!)`, where `⌊N/m⌋` is natural-number division.

This is the exact identity underlying Chebyshev's and Mertens' elementary estimates for the
distribution of primes. -/
theorem vonMangoldt_summatory (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, Λ m * ((N / m : ℕ) : ℝ) = Real.log ((Nat.factorial N : ℕ) : ℝ) := by
  -- The set `{1, …, N}` agrees with the half-open interval `(0, N]`.
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  -- Membership equivalence driving the exchange of summation order.
  have hmem : ∀ (n d : ℕ), n ∈ Finset.Icc 1 N ∧ d ∈ n.divisors ↔
      n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x) ∧ d ∈ Finset.Icc 1 N := by
    intro n d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd, hne⟩
      have hd0 : d ≠ 0 := by rintro rfl; exact hne (Nat.eq_zero_of_zero_dvd hdvd)
      exact ⟨⟨⟨h1, h2⟩, hdvd⟩, Nat.one_le_iff_ne_zero.mpr hd0,
        le_trans (Nat.le_of_dvd (by omega) hdvd) h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, hd1, hdN⟩
      exact ⟨⟨h1, h2⟩, hdvd, by omega⟩
  calc ∑ m ∈ Finset.Icc 1 N, Λ m * ((N / m : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 N,
          ∑ _n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x), Λ d := by
        apply Finset.sum_congr rfl
        intro d _hd
        rw [Finset.sum_const, hset, Nat.Ioc_filter_dvd_card_eq_div N d, nsmul_eq_mul]
        exact mul_comm _ _
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, Λ d := (Finset.sum_comm' hmem).symm
    _ = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n _hn
        exact ArithmeticFunction.vonMangoldt_sum
    _ = Real.log ((Nat.factorial N : ℕ) : ℝ) := (log_factorial_eq_sum_log N).symm

/-- **Upper estimate for `log(N!)`.**

From the summatory identity and `⌊N/m⌋ ≤ N/m` together with `Λ ≥ 0` we obtain
`log(N!) ≤ N · ∑_{m=1}^{N} Λ(m)/m`, the easy half of Mertens' first theorem. -/
theorem log_factorial_le (N : ℕ) :
    Real.log ((Nat.factorial N : ℕ) : ℝ) ≤ (N : ℝ) * ∑ m ∈ Finset.Icc 1 N, Λ m / (m : ℝ) := by
  rw [← vonMangoldt_summatory, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_Icc] at hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hΛ : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  have hcast : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := Nat.cast_div_le
  calc Λ m * ((N / m : ℕ) : ℝ)
      ≤ Λ m * ((N : ℝ) / (m : ℝ)) := mul_le_mul_of_nonneg_left hcast hΛ
    _ = (N : ℝ) * (Λ m / (m : ℝ)) := by ring

end PrimeNumberTheoremOQ03
