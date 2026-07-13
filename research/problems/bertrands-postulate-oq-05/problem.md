# Problem: Every Factorial n! (n ≥ 2) Has a Prime Factor Exceeding n/2

**Slug**: bertrands-postulate-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: bertrands-postulate

## Problem Statement

### Formal Statement

For every $n\ge 2$ there is a prime $p$ with

$$
\frac n2 < p \le n \qquad\text{and}\qquad p \mid n!.
$$

Consequently the largest prime factor of $n!$ exceeds $n/2$, and $n!$ is **never** a perfect
power for $n \ge 2$ (such a prime appears to the first power only).

### Plain Language

The parent entry `bertrands-postulate` proves Bertrand's postulate: for every $m\ge 1$ there
is a prime in $(m, 2m]$. This child combines that with the elementary divisibility fact "every
prime $\le n$ divides $n!$" to pin down a **large** prime factor of the factorial: taking
$m=\lfloor n/2\rfloor$ produces a prime $p$ with $n/2 < p \le n$, and since $p\le n$ it divides
$n!$. A short corollary is that $n!$ cannot be a perfect $k$-th power for $k\ge 2$: this prime
$p$ divides $n!$ but $2p>n$, so $p^2\nmid n!$, giving an odd exponent obstruction.

### Why This Matters

Bertrand's postulate is usually stated purely about the existence of a prime in an interval;
its most useful *corollaries* connect it to factorials, binomial coefficients, and
non-perfect-power results (a classic Erdős-style argument). Mathlib has Bertrand
(`Nat.exists_prime_lt_and_le_two_mul`) and `Nat.Prime.dvd_factorial`, but **no** lemma that
fuses them into "n! has a prime factor in (n/2, n]" or the non-perfect-power corollary. This
is a genuine two-lemma assembly with a small interval-arithmetic bridge.

## Known Results

### What's Already Proven

- Parent `bertrands-postulate` is verified (0-axiom): a prime exists in `(m, 2m]`.
- Mathlib: `Nat.exists_prime_lt_and_le_two_mul` (Bertrand), `Nat.Prime.dvd_factorial`
  (`p.Prime → (p ∣ n! ↔ p ≤ n)`), `Nat.factorization` / `Nat.Prime.factorization_factorial`
  (Legendre) for the perfect-power corollary.

### What's Still Open

- The large-prime-factor theorem and the non-perfect-power corollary (currently `sorry`).

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**number theory / corollary completion**.

## Target Lean Sketch

```lean
open Nat

/-- Combining Bertrand with `dvd_factorial`: `n!` has a prime factor in `(n/2, n]`. -/
theorem factorial_has_large_prime_factor {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n / 2 < p ∧ p ≤ n ∧ p ∣ n.factorial := by
  sorry
  -- Let m = n / 2 (m ≥ 1 since n ≥ 2). Bertrand gives prime p with m < p ≤ 2*m ≤ n.
  --   (2 * (n/2) ≤ n via `Nat.two_mul_div_two_le` / `Nat.div_mul_le_self`.)
  -- Then p ≤ n gives p ∣ n! by `Nat.Prime.dvd_factorial`. Package the four conjuncts.

/-- The witnessing prime appears to the first power only: `p^2 ∤ n!`. -/
theorem large_prime_factor_sq_not_dvd {n : ℕ} (hn : 2 ≤ n)
    {p : ℕ} (hp : p.Prime) (hlo : n / 2 < p) (hhi : p ≤ n) :
    ¬ p ^ 2 ∣ n.factorial := by
  sorry
  -- Legendre: v_p(n!) = ∑_{i≥1} ⌊n/p^i⌋. Here ⌊n/p⌋ = 1 (since n/2 < p ≤ n) and ⌊n/p^i⌋ = 0
  -- for i ≥ 2 (p^2 > n because 2p > n and p ≥ 2 give p^2 ≥ 2p > n). So v_p(n!) = 1 < 2.

/-- Corollary: `n!` is not a perfect square for `n ≥ 2`. -/
theorem factorial_not_isSquare {n : ℕ} (hn : 2 ≤ n) : ¬ IsSquare (n.factorial) := by
  sorry
  -- A square has all even `p`-adic valuations; the prime above has valuation 1.
```

Add worked `example`s: `n = 4` → prime `3 ∈ (2,4]`, `3 ∣ 24`, `9 ∤ 24`, `24` not a square;
`n = 10` → prime `7 ∈ (5,10]`, `7 ∣ 10!`, `49 ∤ 10!`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `bertrands-postulate` | Parent: prime in `(m, 2m]` | analytic number theory |
| `kummer-theorem` | `p`-adic valuation of binomials/factorials (Legendre) | number theory |
| `infinitude-primes` | Factorial-divisibility prime arguments | elementary number theory |

## Tractability Assessment

**Difficulty**: Low-Medium

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The main theorem is Bertrand plus `dvd_factorial` with a one-line
`2*(n/2) ≤ n` bridge. The `p²∤n!` corollary needs Legendre's valuation formula (in Mathlib)
and the interval bound `p² > n`; the non-square corollary is then a valuation-parity argument.

### Suggested First Steps

1. Prove `factorial_has_large_prime_factor`: set `m = n/2`, apply Bertrand, bound
   `2*m ≤ n`, then `Nat.Prime.dvd_factorial`.
2. Prove `p² > n` from `n/2 < p` (so `n < 2p ≤ p²` since `p ≥ 2`).
3. Use `Nat.Prime.factorization_factorial` (Legendre) to get `v_p(n!) = 1`, then conclude
   `p² ∤ n!` and non-squareness by valuation parity.

## References

### Mathlib

- `Nat.exists_prime_lt_and_le_two_mul` — NumberTheory/Bertrand.lean
- `Nat.Prime.dvd_factorial` — Data/Nat/Prime/Factorial.lean
- `Nat.Prime.factorization_factorial` (Legendre) — NumberTheory/Padics/PadicVal.lean
- `Nat.div_mul_le_self`, `Nat.two_mul` — Data/Nat/Defs.lean

### Literature

- Erdős's proof of Bertrand's postulate and its factorial/binomial corollaries; the
  "largest prime factor of `n!` exceeds `n/2`" statement is a standard exercise (Aigner–Ziegler,
  *Proofs from THE BOOK*, Ch. 2).

## Metadata

```yaml
tags:
  - number-theory
  - bertrands-postulate
  - factorials
  - prime-factorization
related_proofs:
  - bertrands-postulate
  - kummer-theorem
  - infinitude-primes
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
