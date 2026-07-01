import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-
# Bertrand's Postulate, oq-05: A Large Prime Factor of `n!`, and the Non-Squareness of Factorials

## Open question (`bertrands-postulate-oq-05`)

Bertrand's postulate guarantees a prime in every interval `(m, 2m]`. Applying it to
`m = ⌊n/2⌋` produces a prime `p` with `n/2 < p ≤ n`. Two structural facts follow, and
together they upgrade Bertrand from an *existence-of-primes* statement into a statement
about the arithmetic of the factorial itself:

* **A large prime factor.** Since `p ≤ n`, the prime divides `n!`. So every `n ≥ 2`
  satisfies `∃ prime p, n < 2p ∧ p ∣ n!` — the factorial always has a prime factor
  exceeding `n/2`.

* **The prime is *unramified* in `n!`.** Because `p ≤ n < 2p` we have `⌊n/p⌋ = 1`, and
  because `p² > n` every higher Legendre term `⌊n/pᵏ⌋` (`k ≥ 2`) vanishes. Hence
  Legendre's formula gives the exact `p`-adic valuation `vₚ(n!) = 1`: the prime divides
  `n!` but `p²` does not.

* **`n!` is never a perfect square for `n ≥ 2`.** If `n! = k²`, the prime `p` above would
  divide `k`, forcing `p² ∣ k² = n!` — contradicting `vₚ(n!) = 1`. This is the classical
  Erdős-style corollary of Bertrand's postulate.

Everything is assembled from Mathlib primitives: `Nat.exists_prime_lt_and_le_two_mul`
(Bertrand), `Nat.dvd_factorial`, Legendre's theorem `padicValNat_factorial`, and
`Nat.Prime.pow_dvd_iff_le_factorization`. Fully machine-checked; no axioms beyond
Mathlib's foundations.
-/

namespace BertrandsPostulateOQ05

open Nat

/-- **Bertrand in the lower half.** For `n ≥ 2` there is a prime `p` with `n/2 < p ≤ n`,
phrased as `n < 2p` (i.e. `p > n/2`) together with `p ≤ n`. Obtained by applying
Bertrand's postulate to `⌊n/2⌋`. -/
theorem exists_prime_gt_half_le {n : ℕ} (hn : 2 ≤ n) :
    ∃ p, p.Prime ∧ n < 2 * p ∧ p ≤ n := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  -- `hlt : n / 2 < p`, `hle : p ≤ 2 * (n / 2)`; `omega` knows the floor-division facts.
  exact ⟨p, hp, by omega, by omega⟩

/-- **Legendre valuation of the large prime is exactly one.** For a prime `p` with
`p ≤ n < 2p`, the `p`-adic valuation of `n!` equals `1`: only the first Legendre term
`⌊n/p⌋ = 1` survives, since `p² > n`. -/
theorem factorization_factorial_eq_one {n p : ℕ} (hp : p.Prime)
    (h2p : n < 2 * p) (hpn : p ≤ n) : (n !).factorization p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p² > n`, so the base-`p` logarithm of `n` is below `2`.
  have hp2 : n < p ^ 2 := by
    have h2 : 2 ≤ p := hp.two_le
    calc n < 2 * p := h2p
      _ ≤ p * p := by nlinarith
      _ = p ^ 2 := (pow_two p).symm
  have hlog : Nat.log p n < 2 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (by have := hp.pos; omega)).2 hp2
  -- Legendre's formula collapses to the single term `⌊n / p⌋ = 1`.
  rw [Nat.factorization_def _ hp, padicValNat_factorial hlog]
  have hset : (Finset.Ico 1 2) = {1} := by decide
  rw [hset, Finset.sum_singleton, pow_one]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The large prime `p` from Bertrand appears in `n!` **to the first power only**:
`p² ∤ n!`. Immediate from `vₚ(n!) = 1`. -/
theorem not_prime_sq_dvd_factorial {n p : ℕ} (hp : p.Prime)
    (h2p : n < 2 * p) (hpn : p ≤ n) : ¬ p ^ 2 ∣ n ! := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.factorial_ne_zero n),
      factorization_factorial_eq_one hp h2p hpn]
  omega

/-- **A prime factor exceeding `n/2`.** Every factorial `n!` with `n ≥ 2` has a prime
factor `p` with `n < 2p`, equivalently `p > n/2`. -/
theorem exists_large_prime_factor {n : ℕ} (hn : 2 ≤ n) :
    ∃ p, p.Prime ∧ n < 2 * p ∧ p ∣ n ! := by
  obtain ⟨p, hp, h2p, hpn⟩ := exists_prime_gt_half_le hn
  exact ⟨p, hp, h2p, Nat.dvd_factorial hp.pos hpn⟩

/-- **`n!` is never a perfect square for `n ≥ 2`.** The Bertrand prime `p` with
`n/2 < p ≤ n` divides `n!` exactly once, so `n!` cannot be a square. -/
theorem factorial_not_isSquare {n : ℕ} (hn : 2 ≤ n) : ¬ IsSquare (n !) := by
  obtain ⟨p, hp, h2p, hpn⟩ := exists_prime_gt_half_le hn
  have hdvd : p ∣ n ! := Nat.dvd_factorial hp.pos hpn
  have hnsq : ¬ p ^ 2 ∣ n ! := not_prime_sq_dvd_factorial hp h2p hpn
  rintro ⟨k, hk⟩
  -- `hk : n ! = k * k`.
  apply hnsq
  have hpk : p ∣ k := by
    have hmul : p ∣ k * k := hk ▸ hdvd
    rcases (hp.dvd_mul).1 hmul with h | h <;> exact h
  rw [hk, pow_two]
  exact mul_dvd_mul hpk hpk

/-- **Capstone.** For every `n ≥ 2` there is a prime `p` with `n < 2p` that divides `n!`
exactly once (`p ∣ n!` but `p² ∤ n!`); consequently `n!` is not a perfect square. -/
theorem bertrand_factorial_summary {n : ℕ} (hn : 2 ≤ n) :
    (∃ p, p.Prime ∧ n < 2 * p ∧ p ∣ n ! ∧ ¬ p ^ 2 ∣ n !) ∧ ¬ IsSquare (n !) := by
  obtain ⟨p, hp, h2p, hpn⟩ := exists_prime_gt_half_le hn
  refine ⟨⟨p, hp, h2p, Nat.dvd_factorial hp.pos hpn,
    not_prime_sq_dvd_factorial hp h2p hpn⟩, factorial_not_isSquare hn⟩

-- Sanity checks on small factorials.
example : ¬ IsSquare (5 !) := factorial_not_isSquare (by norm_num)
example : ¬ IsSquare (10 !) := factorial_not_isSquare (by norm_num)

end BertrandsPostulateOQ05
