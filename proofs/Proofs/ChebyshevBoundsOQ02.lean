import Mathlib

/-
# Chebyshev Bounds OQ-02: The Second Chebyshev Function ψ and Legendre's Identity

## Open Question (parent chebyshev-bounds, second open question)

The parent develops explicit bounds on π(n) and θ(n) = ∑_{p ≤ n} log p via central binomial
coefficients. One listed open direction is the **second Chebyshev function**
`ψ(x) = ∑_{p^k ≤ x} log p` and the partial-summation machinery linking it to θ and to the
Prime Number Theorem.

## What this file proves

The second Chebyshev function is, in von Mangoldt form, `ψ(n) = ∑_{m ≤ n} Λ(m)`, where
`Λ(m) = log p` if `m = p^k` is a prime power and `0` otherwise (Mathlib's
`ArithmeticFunction.vonMangoldt`). The keystone connecting ψ to the factorial — the identity at
the heart of Chebyshev's elementary method — is **Legendre's identity**:

> **`log(n!) = ∑_{d=1}^{n} Λ(d) · ⌊n/d⌋`.**

It follows by writing `log(n!) = ∑_{m≤n} log m`, expanding each `log m = ∑_{d ∣ m} Λ(d)`
(Mathlib's `vonMangoldt_sum`), and swapping the order of summation: each `d ≤ n` contributes
`Λ(d)` once for each of its `⌊n/d⌋` multiples in `[1,n]`. This identity is exactly what powers
the Chebyshev bounds `θ(n), ψ(n) = Θ(n)` (via `log(2n)! − 2·log n! ` telescoping), so it is the
right elementary foundation for this thread.

We also record the basic structure of ψ (nonnegativity, monotonicity) and the bound
`ψ(n) ≤ log(n!)`.

Tags: number-theory, primes, chebyshev, von-mangoldt, prime-counting, analytic-number-theory
-/

open Finset ArithmeticFunction

namespace ChebyshevBoundsOQ02

/-- The **second Chebyshev function** `ψ(n) = ∑_{m ≤ n} Λ(m) = ∑_{p^k ≤ n} log p`, in von
    Mangoldt form. -/
noncomputable def chebyshevPsi (n : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 n, Λ m

/-- ψ is nonnegative (von Mangoldt is nonnegative). -/
theorem chebyshevPsi_nonneg (n : ℕ) : 0 ≤ chebyshevPsi n :=
  Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg

/-- ψ is monotone in `n`. -/
theorem chebyshevPsi_mono {m n : ℕ} (h : m ≤ n) : chebyshevPsi m ≤ chebyshevPsi n :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right h) (fun _ _ _ => vonMangoldt_nonneg)

/-
═══════════════════════════════════════════════════════════════════════════════
LEGENDRE'S IDENTITY: log(n!) = ∑_{d≤n} Λ(d)·⌊n/d⌋
═══════════════════════════════════════════════════════════════════════════════
-/

/-- `∏_{m=1}^{n} m = n!`. -/
theorem prod_Icc_id_eq_factorial (n : ℕ) : ∏ m ∈ Finset.Icc 1 n, m = Nat.factorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]

/-- For `m ∈ [1,n]`, the divisors of `m` are exactly the elements of `[1,n]` dividing `m`. -/
theorem divisors_eq_filter {m n : ℕ} (hm : m ∈ Finset.Icc 1 n) :
    m.divisors = (Finset.Icc 1 n).filter (· ∣ m) := by
  rw [Finset.mem_Icc] at hm
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, hm0⟩
    exact ⟨⟨Nat.pos_of_mem_divisors (Nat.mem_divisors.2 ⟨hd, hm0⟩),
      (Nat.le_of_dvd (by omega) hd).trans hm.2⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, by omega⟩

/-- The number of multiples of `d` in `[1,n]` is `⌊n/d⌋`. -/
theorem card_multiples_Icc (d n : ℕ) :
    ((Finset.Icc 1 n).filter (d ∣ ·)).card = n / d := by
  have hset : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div]

/-- **Legendre's identity** (the Chebyshev/Legendre formula): the logarithm of `n!` is the
    weighted sum of von Mangoldt values, each `Λ(d)` counted `⌊n/d⌋` times.

    `log(n!) = ∑_{d=1}^{n} Λ(d) · ⌊n/d⌋`. -/
theorem log_factorial_eq_sum (n : ℕ) :
    Real.log (Nat.factorial n : ℝ) = ∑ d ∈ Finset.Icc 1 n, Λ d * (n / d : ℕ) := by
  -- log(n!) = ∑_{m≤n} log m
  have hfact : Real.log (Nat.factorial n : ℝ) = ∑ m ∈ Finset.Icc 1 n, Real.log (m : ℝ) := by
    rw [← prod_Icc_id_eq_factorial, Nat.cast_prod, Real.log_prod]
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact_mod_cast (Nat.cast_pos.2 (by omega : 0 < m)).ne'
  rw [hfact]
  -- each log m = ∑_{d ∣ m} Λ d
  have hstep : ∀ m ∈ Finset.Icc 1 n, Real.log (m : ℝ) =
      ∑ d ∈ Finset.Icc 1 n, (if d ∣ m then Λ d else 0) := by
    intro m hm
    rw [← vonMangoldt_sum, divisors_eq_filter hm, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  -- swap: ∑_d ∑_m (if d∣m then Λ d) = ∑_d Λ d * #{m : d∣m}
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_multiples_Icc, nsmul_eq_mul, mul_comm]

/-- **ψ(n) ≤ log(n!)**: each von Mangoldt term is dominated by the corresponding log. -/
theorem chebyshevPsi_le_log_factorial (n : ℕ) :
    chebyshevPsi n ≤ Real.log (Nat.factorial n : ℝ) := by
  rw [chebyshevPsi, ← prod_Icc_id_eq_factorial, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_le_sum fun m _ => ?_
    simpa using vonMangoldt_le_log
  · intro m hm
    rw [Finset.mem_Icc] at hm
    exact_mod_cast (Nat.cast_pos.2 (by omega : 0 < m)).ne'

end ChebyshevBoundsOQ02

/-
## Summary

The second Chebyshev function ψ in von Mangoldt form and Legendre's identity, the elementary
engine of the Chebyshev bounds:

- `chebyshevPsi`:               ψ(n) = ∑_{m≤n} Λ(m) = ∑_{p^k≤n} log p, with `chebyshevPsi_nonneg`,
  `chebyshevPsi_mono`.
- `log_factorial_eq_sum`:       **log(n!) = ∑_{d≤n} Λ(d)·⌊n/d⌋** (Legendre's identity), via
  log m = ∑_{d∣m} Λ(d) and a summation swap counting multiples.
- `chebyshevPsi_le_log_factorial`: ψ(n) ≤ log(n!).

Uses Mathlib's `ArithmeticFunction.vonMangoldt` (`vonMangoldt_sum`, `vonMangoldt_le_log`) and
`Nat.Ioc_filter_dvd_card_eq_div`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
