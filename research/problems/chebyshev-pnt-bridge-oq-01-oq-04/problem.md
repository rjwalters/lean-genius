# Problem: Multinomial Kummer Carry Bound and π(kn)

**Slug**: chebyshev-pnt-bridge-oq-01-oq-04
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a prime $p$ and the central multinomial coefficient $\binom{kn}{n,n,\dots,n}$ ($k$ blocks of size $n$),

$$
p^{\,v_p\!\left(\binom{kn}{n,\dots,n}\right)} \le kn,
$$

and consequently a Chebyshev-type lower bound $\pi(kn) \gtrsim \dfrac{\log \binom{kn}{n,\dots,n}}{\log(kn)}$.

### Plain Language

The parent proof `chebyshev-pnt-bridge-oq-01` formalizes $p^{v_p(\binom{2n}{n})} \le 2n$ via Kummer's theorem (a prime power dividing the central binomial coefficient is at most $2n$), the key input to Chebyshev's elementary bounds on $\pi(x)$. This problem generalizes from binomial ($k=2$) to **multinomial** ($k \ge 2$) coefficients: Kummer's theorem counts base-$p$ carries when adding several numbers, so the same one-line valuation bound should extend, yielding a lower bound on $\pi(kn)$.

### Why This Matters

Elementary Chebyshev-type bounds on the prime-counting function are a cornerstone of analytic number theory before the full PNT. Extending the carry-counting core to multinomials broadens the elementary toolkit and directly exercises Mathlib's factorization API in a multi-term setting.

## Known Results

### What's Already Proven
- $p^{v_p(\binom{2n}{n})} \le 2n$ — gallery `chebyshev-pnt-bridge-oq-01`.
- Kummer's theorem / `Nat.pow_factorization_choose_le` — Mathlib (binomial form).
- Legendre's formula for $v_p(m!)$ — Mathlib.

### What's Still Open (for formalization)
- The multinomial valuation bound $p^{v_p} \le kn$.
- The resulting $\pi(kn)$ lower bound in elementary form.

### Our Goal
Prove the multinomial valuation bound in Lean (via Legendre's formula for $v_p(m!)$ applied to $\frac{(kn)!}{(n!)^k}$ and the carry interpretation), then derive the Chebyshev-style lower bound on $\pi(kn)$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chebyshev-pnt-bridge-oq-01 | Direct parent; binomial case | Kummer, Legendre |
| infinitude-primes | Prime counting context | — |

## Initial Thoughts

### Potential Approaches
1. **Legendre-formula route**: write $v_p\!\big(\tfrac{(kn)!}{(n!)^k}\big) = \sum_{i\ge 1}\big(\lfloor kn/p^i\rfloor - k\lfloor n/p^i\rfloor\big)$; the bound $p^{v_p}\le kn$ follows from summing only over $p^i \le kn$.
2. **Direct carry counting**: adapt Mathlib's binomial `pow_factorization_choose_le` proof to the multinomial factorization.

### Key Difficulties
- Mathlib's multinomial-coefficient API is thinner than the binomial one; may need `Nat.multinomial` lemmas.
- Bounding the number of nonzero carry terms by $\log_p(kn)$.

### What Would a Proof Need?
- Lemma: $v_p\!\big(\binom{kn}{n,\dots,n}\big) \le \log_p(kn)$.
- Bridge from valuation bound to $\pi$ lower bound.

## Tractability Assessment

**Difficulty**: Medium (leaning tractable)

**Justification**: The parent's one-line core (`Nat.pow_factorization_choose_le`) strongly suggests a direct multinomial analogue; the main work is API plumbing for `Nat.multinomial`.

## References

### Texts
- Nathanson, *Elementary Methods in Number Theory* (Chebyshev bounds).

### Mathlib
- `Nat.pow_factorization_choose_le`, `Nat.multinomial`, `Nat.Prime.factorization_factorial`, `Nat.primeCounting`.

## Metadata

```yaml
tags:
  - number-theory
  - analytic-number-theory
  - kummer
  - chebyshev
related_proofs:
  - chebyshev-pnt-bridge-oq-01
  - infinitude-primes
difficulty: medium
source: gallery-gap
created: 2026-07-04
```
