# Problem: Central-binomial closed form of the symmetric Beta integral B(n+1,n+1)

**Slug**: beta-integral-recurrence-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
B(n+1,\,n+1) \;=\; \int_0^1 t^n (1-t)^n \, dt \;=\; \frac{(n!)^2}{(2n+1)!} \;=\; \frac{1}{(2n+1)\binom{2n}{n}}.
$$

### Plain Language

The parent entry (`beta-integral-recurrence-oq-01`) establishes the Beta integral recurrence and its
integer closed form $B(m,k) = \tfrac{(m-1)!\,(k-1)!}{(m+k-1)!}$. This leaf specializes to the
**symmetric diagonal** $m = k = n+1$, giving the central-binomial / Wallis-type value
$B(n+1,n+1) = \tfrac{(n!)^2}{(2n+1)!}$, and rewrites it in terms of the central binomial coefficient
as $\tfrac{1}{(2n+1)\binom{2n}{n}}$.

### Why This Matters

The symmetric Beta integral $B(n+1,n+1)$ is exactly the normalizing constant of the symmetric
$\mathrm{Beta}(n+1,n+1)$ density on $[0,1]$ (a polynomial bump concentrated at $t=\tfrac12$). The
closed form ties the analytic integral to the discrete central binomial coefficient $\binom{2n}{n}$,
and the $\tfrac{1}{(2n+1)\binom{2n}{n}}$ form is the cleanest bridge to Wallis-product and
catalan-number identities.

### Why $(n!)^2/(2n+1)!$

From the integer closed form with $m=k=n+1$: $B(n+1,n+1)=\tfrac{n!\,n!}{(2n+1)!}$. Using
$(2n+1)! = (2n+1)\cdot(2n)!$ and $\binom{2n}{n}=\tfrac{(2n)!}{(n!)^2}$, this equals
$\tfrac{1}{(2n+1)}\cdot\tfrac{(n!)^2}{(2n)!} = \tfrac{1}{(2n+1)\binom{2n}{n}}$.

## Known Results

### What's Already Proven

- Parent `beta-integral-recurrence-oq-01`: integer closed form $B(m,k)=\tfrac{(m-1)!(k-1)!}{(m+k-1)!}$ (verified).
- Mathlib: `Real.betaIntegral`, `Real.Beta`, the Beta–Gamma relation, and `Nat.choose`/factorial API.

### What's Still Open

- The symmetric specialization and its central-binomial rewrite (this entry).

### Our Goal

Prove $B(n+1,n+1) = \tfrac{(n!)^2}{(2n+1)!} = \tfrac{1}{(2n+1)\binom{2n}{n}}$ by specializing the
parent's closed form, then discharging the central-binomial rewrite with `Nat.choose` factorial
identities (`Nat.choose_mul_factorial_le` / `Nat.add_choose` style) and `field_simp`/`ring`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| beta-integral-recurrence-oq-01 | Direct parent; integer closed form of B(m,k) | betaIntegral, Beta–Gamma |
| gamma-reflection-formula-oq-01-oq-01-oq-01 | Symmetric Beta values B(s,1-s) | Gamma reflection |
| combinations-formula-oq-02-oq-01 | Central binomial / Catalan generating function | binomial coefficients |

## Initial Thoughts

### Potential Approaches

1. **Specialize the parent closed form**: set $m=k=n+1$ in $B(m,k)=\tfrac{(m-1)!(k-1)!}{(m+k-1)!}$
   and simplify $(n+1+n+1-1)! = (2n+1)!$.
   - Why it might work: the parent already did the hard analytic work; this is arithmetic.
   - Risk: the central-binomial rewrite needs $\binom{2n}{n}(n!)^2 = (2n)!$ as a `Nat` identity,
     then casting to `ℝ` with `Nat.cast_*` lemmas before `field_simp`.

### Key Difficulties

- Converting the factorial closed form into the $\tfrac{1}{(2n+1)\binom{2n}{n}}$ form requires the
  central-binomial factorial identity and careful `Nat` → `ℝ` casts (avoid division-by-zero traps).

### What Would a Proof Need?

- Key lemma 1: $B(n+1,n+1) = \tfrac{(n!)^2}{(2n+1)!}$ from the parent (direct specialization).
- Key lemma 2: $\binom{2n}{n}\cdot (n!)^2 = (2n)!$ and $(2n+1)! = (2n+1)(2n)!$.
- Final: `field_simp`/`ring` (or `norm_num`) to combine into $\tfrac{1}{(2n+1)\binom{2n}{n}}$.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The analytic content is inherited from the verified parent; the remaining work is factorial/binomial
  algebra with established Mathlib lemmas.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Gamma.Beta` — `Real.betaIntegral`, Beta–Gamma relation.
- `Mathlib.Data.Nat.Choose.Basic` / `Mathlib.Data.Nat.Factorial.BigOperators` — central binomial identities.

## Metadata

```yaml
tags:
  - analysis
  - beta-function
  - binomial-coefficients
  - wallis
related_proofs:
  - beta-integral-recurrence-oq-01
  - gamma-reflection-formula-oq-01-oq-01-oq-01
  - combinations-formula-oq-02-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
