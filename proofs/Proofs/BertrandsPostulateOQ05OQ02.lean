import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-
# Bertrand's Postulate, oq-05-oq-02: An Unramified-Prime API for Factorials

## Open question (`bertrands-postulate-oq-05-oq-02`)

The parent entry `bertrands-postulate-oq-05` computes the exact `p`-adic valuation
`vₚ(n!) = 1` for the *single* Bertrand prime `p ∈ (n/2, n]`, exploiting that `p² > n`
kills every Legendre term beyond the first and that `⌊n/p⌋ = 1` in that narrow window.
Its second listed open question asks whether the valuation-collapse lemma generalizes:

> Can the valuation-collapse lemma be generalized to `vₚ(n!) = ⌊n/p⌋` whenever `p² > n`
> (a prime in `(√n, n]`), giving a reusable "unramified prime" API for factorials?

This file answers it. For **any** prime `p` with `p² > n` (equivalently `p > √n`, no upper
bound on `p` relative to `n` required), Legendre's formula
`vₚ(n!) = Σ_{i≥1} ⌊n/pⁱ⌋` collapses to its single first term, so

  `vₚ(n!) = ⌊n/p⌋`.

Everything downstream is then controlled by that one floor:

* `factorization_factorial_of_sq_gt` — the exact valuation `vₚ(n!) = ⌊n/p⌋`.
* `padicValNat_factorial_of_sq_gt` — same statement for the raw `padicValNat`.
* `prime_pow_dvd_factorial_iff_of_sq_gt` — `pᵏ ∣ n! ↔ k ≤ ⌊n/p⌋`, the full divisibility API.
* `prime_pow_div_dvd_factorial` — the exact power: `p^⌊n/p⌋ ∣ n!` but `p^(⌊n/p⌋+1) ∤ n!`.
* `factorization_factorial_eq_one` — recovers the parent's `vₚ(n!) = 1` as the special case
  `p ≤ n < 2p` (where `⌊n/p⌋ = 1`).
* `unramified_prime_factorial` — capstone bundling valuation and divisibility.

The generalization is strictly wider than the parent: the parent needs `p ≤ n < 2p`, whereas
here `p` may be *any* prime above `√n`, including primes far larger than `n` (where
`⌊n/p⌋ = 0`, correctly giving `vₚ(n!) = 0`). Fully machine-checked; no axioms beyond
Mathlib's foundations, no `native_decide`.
-/

namespace BertrandsPostulateOQ05OQ02

open Nat

/-- **Legendre collapse for large primes.** If a prime `p` satisfies `p² > n` (equivalently
`p > √n`), then only the first term of Legendre's formula survives and the `p`-adic
valuation of `n!` is exactly `⌊n/p⌋`. No relationship between `p` and `n` beyond `n < p²` is
needed: for `p > n` this correctly returns `0`, and for `√n < p ≤ n` it returns `⌊n/p⌋ ≥ 1`. -/
theorem factorization_factorial_of_sq_gt {n p : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    (n !).factorization p = n / p := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p² > n` forces the base-`p` logarithm of `n` below `2`, so Legendre's sum runs over
  -- `Ico 1 2 = {1}` only.
  have hlog : Nat.log p n < 2 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · exact (Nat.log_lt_iff_lt_pow hp.one_lt h0.ne').2 hn
  rw [Nat.factorization_def _ hp, padicValNat_factorial hlog]
  have hset : Finset.Ico 1 2 = {1} := by decide
  rw [hset, Finset.sum_singleton, pow_one]

/-- The same collapse phrased with the raw `padicValNat`. -/
theorem padicValNat_factorial_of_sq_gt {n p : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    padicValNat p (n !) = n / p := by
  rw [← Nat.factorization_def _ hp]
  exact factorization_factorial_of_sq_gt hp hn

/-- **The full divisibility API.** For a prime with `p² > n`, `pᵏ ∣ n!` holds precisely when
`k ≤ ⌊n/p⌋`: the entire divisibility behaviour of `p` in `n!` is governed by the single
floor `⌊n/p⌋`. -/
theorem prime_pow_dvd_factorial_iff_of_sq_gt {n p k : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    p ^ k ∣ n ! ↔ k ≤ n / p := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.factorial_ne_zero n),
      factorization_factorial_of_sq_gt hp hn]

/-- **The exact power.** For a prime with `p² > n`, `p^⌊n/p⌋` divides `n!` while
`p^(⌊n/p⌋+1)` does not — `⌊n/p⌋` is the precise exponent of `p` in `n!`. -/
theorem prime_pow_div_dvd_factorial {n p : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    p ^ (n / p) ∣ n ! ∧ ¬ p ^ (n / p + 1) ∣ n ! := by
  refine ⟨(prime_pow_dvd_factorial_iff_of_sq_gt hp hn).2 le_rfl, ?_⟩
  rw [prime_pow_dvd_factorial_iff_of_sq_gt hp hn]
  omega

/-- **Recovering the parent's `vₚ(n!) = 1`** (`bertrands-postulate-oq-05`). The Bertrand
prime `p ∈ (n/2, n]` satisfies `p ≤ n < 2p`, which forces both `p² > n` and `⌊n/p⌋ = 1`, so
the general collapse specializes to valuation exactly one. -/
theorem factorization_factorial_eq_one {n p : ℕ} (hp : p.Prime)
    (h2p : n < 2 * p) (hpn : p ≤ n) : (n !).factorization p = 1 := by
  have hn : n < p ^ 2 := by
    have h2 : 2 ≤ p := hp.two_le
    calc n < 2 * p := h2p
      _ ≤ p * p := by nlinarith
      _ = p ^ 2 := (pow_two p).symm
  rw [factorization_factorial_of_sq_gt hp hn]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- **Capstone: the unramified-prime API.** For any prime `p` with `p² > n`, the entire
`p`-adic behaviour of `n!` is governed by the single floor `⌊n/p⌋`: the valuation equals
`⌊n/p⌋`, and `pᵏ ∣ n!` iff `k ≤ ⌊n/p⌋`. -/
theorem unramified_prime_factorial {n p : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    (n !).factorization p = n / p ∧ ∀ k, (p ^ k ∣ n ! ↔ k ≤ n / p) :=
  ⟨factorization_factorial_of_sq_gt hp hn,
    fun _ => prime_pow_dvd_factorial_iff_of_sq_gt hp hn⟩

-- Worked example: `11² = 121 > 100`, and `⌊100/11⌋ = 9`, so `v₁₁(100!) = 9`
-- (Legendre: `⌊100/11⌋ + ⌊100/121⌋ = 9 + 0`).
example : (100 !).factorization 11 = 9 := by
  rw [factorization_factorial_of_sq_gt (by norm_num) (by norm_num)]

-- A prime larger than `n` is unramified with valuation `0`: `13² = 169 > 10`, `⌊10/13⌋ = 0`.
example : (10 !).factorization 13 = 0 := by
  rw [factorization_factorial_of_sq_gt (by norm_num) (by norm_num)]

end BertrandsPostulateOQ05OQ02
