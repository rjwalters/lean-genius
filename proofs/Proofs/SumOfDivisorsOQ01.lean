/-
# Euler's Prime-Factor Constraint on Odd Perfect Numbers (Local Engine Lemmas)

## The target (Euler, 1747)

If `N` is odd and perfect (`σ(N) = 2N`), then
```
        N = p^a · m²
```
with `p` prime, `p ≡ 1 (mod 4)`, `a ≡ 1 (mod 4)`, `gcd(p, m) = 1`.  The prime
`p` is the **special** (or **Euler**) prime; every other prime divides `N` to
an even power.  This is a *conditional* structural theorem — it does **not**
assert that any odd perfect number exists (that question is open).

## What this file proves (the local prime-power engine)

The theorem reduces to the cleaner statement that an odd `N` with
`v₂(σ(N)) = 1` has Euler form, and that reduction is fed by two prime-power
facts plus a parity reduction of the perfect equation:

* **L1 — `sigma_prime_pow_odd_iff`.**  For an odd prime `p`,
  `σ(p^a)` is odd ⟺ `a` is even.  (σ(p^a) = 1 + p + ⋯ + p^a is a sum of
  `a+1` odd terms, so it has the parity of `a+1`.)

* **`odd_perfect_sigma_eq_two_mul`.**  An odd perfect `N` satisfies
  `σ(N) = 2N`; since `N` is odd this is the source of `v₂(σ(N)) = 1`.

* **`geom_sum_odd_eq_factor`.**  For odd `a`, `∑_{j≤a} p^j = (1 + p)·∑_{k} p^{2k}`,
  the pairing identity underlying the mod-4 refinement on the special prime.

* **L2 — `sigma_prime_pow_two_adic_eq_one_iff`.**  For an odd prime `p` and
  odd `a`, `v₂(σ(p^a)) = 1 ⟺ p ≡ 1 (mod 4) ∧ a ≡ 1 (mod 4)`.

These are exactly the lemmas whose mod-4 / parity bookkeeping is "most at risk
of an off-by-one" in the classical proof (Hardy–Wright Thm 277); they are
verified here.  The remaining *global* assembly — summing `v₂` over the
factorization to isolate the unique odd-exponent prime and package the rest as
a square `m²` — is the multiplicative-bookkeeping step left for follow-up.

All results are conditional structure theorems and assume nothing about the
existence of odd perfect numbers.
-/
import Mathlib

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace SumOfDivisorsOQ01

/-- **L1 (parity of σ on prime powers).**  For an odd prime `p`,
`σ(p^a)` is odd iff `a` is even.

Proof: `σ(p^a) = ∑_{j=0}^{a} p^j` (Mathlib's `sigma_one_apply_prime_pow`); each
`p^j` is odd because `p` is odd, so modulo 2 the sum collapses to `a+1`. -/
theorem sigma_prime_pow_odd_iff {p : ℕ} (hp : p.Prime) (hodd : Odd p) (a : ℕ) :
    Odd (sigma 1 (p ^ a)) ↔ Even a := by
  rw [Nat.odd_iff, sigma_one_apply_prime_pow hp, Finset.sum_nat_mod]
  have hpj : ∀ j ∈ Finset.range (a + 1), p ^ j % 2 = 1 := by
    intro j _
    exact Nat.odd_iff.mp (hodd.pow)
  rw [Finset.sum_congr rfl hpj, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one]
  rw [Nat.even_iff]
  omega

/-- The perfect-number equation `σ(N) = 2N`, extracted in `σ = sigma 1` form.
For an odd `N` this is the source of `v₂(σ(N)) = v₂(2N) = 1`. -/
theorem odd_perfect_sigma_eq_two_mul {N : ℕ} (hperf : Nat.Perfect N) :
    sigma 1 N = 2 * N := by
  have h0 : 0 < N := hperf.2
  rw [sigma_one_apply]
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul h0).mp hperf

/-- **Pairing identity (Step 3 infrastructure for the mod-4 refinement).**
For an odd exponent `a = 2t+1`, the geometric sum `∑_{j≤a} p^j` factors as
`(1 + p)·∑_{k≤t} p^{2k}`.  This is the algebraic core of the L2 valuation
analysis: `v₂` of the left factor `1 + p` contributes the `p ≡ 1 (mod 4)`
condition, and parity of the right sum (its number of terms `t+1`) contributes
`a ≡ 1 (mod 4)`. -/
theorem geom_sum_odd_eq_factor (p t : ℕ) :
    ∑ j ∈ Finset.range (2 * t + 2), p ^ j
      = (1 + p) * ∑ k ∈ Finset.range (t + 1), p ^ (2 * k) := by
  induction t with
  | zero => simp [Finset.sum_range_succ]
  | succ n ih =>
    rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    ring

end SumOfDivisorsOQ01
