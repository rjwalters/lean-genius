# Problem: Repunit Divisibility — $R_m \mid R_n \iff m \mid n$

**Slug**: repunit-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For $n \ge 1$ define the base-10 *repunit*
$$
R_n = \underbrace{11\cdots1}_{n} = \frac{10^n - 1}{9} = \sum_{i=0}^{n-1} 10^i .
$$
Then for all $m, n \ge 1$,
$$
R_m \mid R_n \iff m \mid n .
$$
As supporting / corollary facts: $R_{a+b} = R_a \cdot 10^{b} + R_b$, and
$\gcd(R_m, R_n) = R_{\gcd(m,n)}$ (the "strong divisibility sequence" property,
mirroring the Fibonacci $\gcd$ identity).

### Plain Language

A repunit is a number written as a string of ones: $1, 11, 111, 1111, \dots$.
The claim is that one repunit divides another exactly when the *count of ones*
of the first divides the count of ones of the second — e.g. $R_2 = 11$ divides
$R_6 = 111111$ because $2 \mid 6$. We want a machine-checked proof of this clean
divisibility characterization.

### Why This Matters

Repunits form a *strong divisibility sequence* — the same structural property
that makes Fibonacci/Mersenne divisibility work ($\gcd(a_m, a_n) = a_{\gcd(m,n)}$).
Formalizing the repunit case both produces a self-contained gallery result and
exercises geometric-series / `Nat`-divisibility reasoning. The general statement
reduces to the algebraic fact $\dfrac{x^n - 1}{x - 1}$ divisibility with $x = 10$.

## Known Results

### What's Already Proven

- Classical elementary number theory: $R_m \mid R_n \iff m \mid n$, and more
  generally $\gcd(R_m, R_n) = R_{\gcd(m,n)}$.
- Mathlib provides $x - 1 \mid x^n - 1$ and the finite geometric sum
  $\sum_{i<n} x^i = (x^n-1)/(x-1)$ machinery (`Finset.geom_sum_eq`,
  `geom_sum_mul`, `Mathlib.Algebra.GeomSum`).

### What's Still Open (engineering)

- No Lean/Mathlib or gallery formalization of repunit divisibility as a named
  result.

### Our Goal

Define `R n := ∑ i ∈ Finset.range n, 10 ^ i` (avoiding `Nat` division), prove the
splitting identity `R (a + b) = R a * 10 ^ b + R b`, derive `R m ∣ R (m * k)` by
induction on $k$, and prove the converse via the division-with-remainder
argument $n = qm + r$ with $0 \le r < m$ forcing $r = 0$. Optionally land
`Nat.gcd (R m) (R n) = R (Nat.gcd m n)`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sylvester-sequence-oq-01 | divisibility/coprimality of a recursively defined integer sequence | telescoping, induction |
| stern-brocot-tree-oq-01 | gcd-structured integer sequences | gcd recurrences |
| midy-theorem-oq-01 | base-10 repetend / $10^k - 1$ arithmetic | order of 10 mod m |

## Initial Thoughts

### Potential Approaches

1. **Forward (`m ∣ n ⟹ R_m ∣ R_n`) by the splitting identity**: write
   $n = m k$, induct on $k$ using $R_{m(k+1)} = R_{mk}\cdot 10^{m} + R_{m}$, so
   $R_m \mid R_{mk}$ and $R_m \mid R_m$ give $R_m \mid R_{m(k+1)}$.
   - Why it might work: the additive split is a one-line `Finset.range` sum
     manipulation; induction is routine.

2. **Converse (`R_m ∣ R_n ⟹ m ∣ n`)**: divide $n = qm + r$, $0 \le r < m$. Then
   $R_n = R_{qm}\cdot 10^{r} + R_r$ and $R_m \mid R_{qm}$, so $R_m \mid R_n$
   forces $R_m \mid R_r$; but $0 \le r < m \Rightarrow R_r < R_m$, hence $R_r = 0$,
   i.e. $r = 0$.
   - Risk: bookkeeping on the $R_r < R_m$ strict bound for $r < m$.

### Key Difficulties

- Working with the integer sum form $\sum 10^i$ rather than $(10^n-1)/9$ to dodge
  `Nat` truncated division entirely.
- The strict inequality $R_r < R_m$ for $r < m$ (monotonicity of $R$).

### What Would a Proof Need?

- `def R (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i`
- `R_add : R (a + b) = R a * 10 ^ b + R b`
- `R_strict_mono : a < b → R a < R b`
- forward `dvd` by induction; converse by `Nat.div_add_mod` + strict bound

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The forward direction is a short induction off one additive identity.
- The converse is the standard "remainder must vanish" argument; the only
  fiddly piece is the strict-monotonicity bound, which is elementary.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days ($\iff$); the $\gcd$ corollary adds a day.

## References

### Online Resources
- OEIS A002275 (repunits $R_n = (10^n-1)/9$).
- Standard result; analogous to Fibonacci/Mersenne strong divisibility.

### Mathlib
- `Mathlib.Algebra.GeomSum` — `geom_sum_mul`, `Commute.geom_sum_mul`, finite
  geometric sums and $x-1 \mid x^n - 1$.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_range_succ`, range splits.
- `Nat.div_add_mod`, `Nat.mod_lt` — division-with-remainder for the converse.

## Metadata

```yaml
tags:
  - number-theory
  - repunit
  - divisibility
  - geometric-series
  - strong-divisibility-sequence
related_proofs:
  - sylvester-sequence-oq-01
  - stern-brocot-tree-oq-01
  - midy-theorem-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
