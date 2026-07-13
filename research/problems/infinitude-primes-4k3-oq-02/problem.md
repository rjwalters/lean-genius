# Problem: Density 1/φ(d) of Primes in Arithmetic Progressions

**Slug**: infinitude-primes-4k3-oq-02
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `infinitude-primes-4k3`)

## Problem Statement

### Formal Statement

For coprime $a$ and $d$ (i.e. $\gcd(a,d)=1$), the primes $p \equiv a \pmod d$ have natural
density $1/\varphi(d)$ among all primes:

$$
\lim_{x\to\infty} \frac{\#\{p \le x : p\ \text{prime},\ p\equiv a \pmod d\}}{\#\{p\le x : p\ \text{prime}\}} = \frac{1}{\varphi(d)}.
$$

This is the **quantitative** form of Dirichlet's theorem — equivalently the Prime Number Theorem
for arithmetic progressions (PNT-AP). The parent proof handles only the *qualitative* special
case $d=4, a=3$ (infinitely many primes $\equiv 3 \bmod 4$) by an elementary Euclid-style argument.

### Plain Language

The parent shows there are infinitely many primes leaving remainder 3 when divided by 4. This
problem asks the much stronger statement: primes are *equidistributed* among the allowable
remainder classes. For modulus $d$ there are $\varphi(d)$ coprime classes and each gets an equal
$1/\varphi(d)$ share of the primes in the limit.

### Why This Matters

Equidistribution of primes in progressions underpins huge swaths of analytic number theory
(Bombieri–Vinogradov, Chebotarev in the abelian case, etc.). Even *stating* PNT-AP cleanly in
Lean and reducing it to Mathlib's existing analytic inputs is valuable. Mathlib already has
Dirichlet's theorem (infinitude) and PNT; the gap is assembling the *density* statement and the
PNT-AP refinement.

## Known Results

### What's Already Proven

- `infinitude-primes-4k3` — infinitely many primes $\equiv 3 \bmod 4$ (elementary, parent).
- Mathlib: `Nat.setOf_prime_and_eq_mod_infinite` / `Nat.forall_exists_prime_gt_and_eq_mod` (Dirichlet, qualitative); `Nat.ArithmeticFunction` and the Prime Number Theorem (`PrimeCounting`/`Chebyshev`).
- Dirichlet $L$-functions and their nonvanishing at $s=1$ are in Mathlib (`DirichletCharacter`, `LSeries`).

### What's Still Open (in this gallery)

- The density statement $\pi(x;d,a)/\pi(x) \to 1/\varphi(d)$ assembled in Lean.
- The PNT-AP error term $\pi(x;d,a) = \frac{1}{\varphi(d)}\operatorname{Li}(x) + o(\cdot)$.

### Our Goal

State PNT-AP in Lean and prove the density $1/\varphi(d)$ by orthogonality of Dirichlet
characters plus nonvanishing of $L(1,\chi)$ for $\chi\neq\chi_0$, reducing to the analytic facts
already available in Mathlib. A first milestone: the $d=4$ case ($\pi(x;4,1)\sim\pi(x;4,3)\sim\tfrac12\pi(x)$).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| infinitude-primes-4k3 | Direct parent; qualitative special case | Euclid-style construction |
| prime-number-theorem | The unconditional density baseline ($d=1$) | analytic NT, Chebyshev |
| dirichlets-theorem (gallery) | Infinitude in general progressions | $L$-functions, characters |

## Initial Thoughts

### Potential Approaches

1. **Character orthogonality + $L(1,\chi)\neq 0$ (recommended)**: write the indicator of
   $p\equiv a$ as $\frac{1}{\varphi(d)}\sum_\chi \bar\chi(a)\chi(p)$ and pass each character sum
   to its $L$-function asymptotics.
   - Why it might work: this is the standard proof and Mathlib already has characters, $L$-series, and nonvanishing.
   - Risk: extracting the *density/PNT-AP* asymptotic (not just $\sum 1/p$ divergence) may require more analytic plumbing than is currently packaged.

2. **Reduce to Mathlib's PNT + Tauberian inputs**: derive PNT-AP from PNT for each character twist.
   - Why it might work: leverages the hardest analytic lemma already done.
   - Risk: the Tauberian transfer per character is nontrivial.

### Key Difficulties

- Mathlib has Dirichlet infinitude and PNT, but the *combined* PNT-AP density may not be directly available — assembling it is the crux.
- Keeping the character/orthogonality bookkeeping clean over $\mathbb{Z}/d$.

### What Would a Proof Need?

- Key lemma 1: character orthogonality $\frac{1}{\varphi(d)}\sum_\chi \bar\chi(a)\chi(n) = \mathbb{1}[n\equiv a]$.
- Key lemma 2: $\sum_{p\le x}\chi(p) = o(\pi(x))$ for $\chi\neq\chi_0$ (from $L(1,\chi)\neq0$).
- Technical requirements: `DirichletCharacter`, `LSeries`, PNT API, `Nat.totient`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The statement is standard but the quantitative density needs analytic asymptotics beyond mere infinitude.
- Mathlib provides most ingredients (characters, $L$-functions, nonvanishing, PNT) but not the packaged PNT-AP density.
- The $d=4$ milestone is a realistic, well-scoped first deliverable.

**Estimated Effort**:
- Exploration: days–weeks
- If tractable: 1–2 months
- If hard: unknown (if PNT-AP must be built from scratch)

## References

### Papers
- Dirichlet (1837), original theorem on primes in progressions.
- Davenport, *Multiplicative Number Theory* — PNT-AP and $L(1,\chi)\neq 0$.

### Online Resources
- Parent gallery entry `infinitude-primes-4k3`.

### Mathlib
- `Mathlib.NumberTheory.DirichletCharacter` and `Mathlib.NumberTheory.LSeries` — characters and $L$-functions.
- `Mathlib.NumberTheory.PrimeCounting` / PNT — density baseline.

## Metadata

```yaml
tags:
  - number-theory
  - analytic-number-theory
  - primes-in-progressions
  - dirichlet-characters
related_proofs:
  - infinitude-primes-4k3
  - prime-number-theorem
difficulty: high
source: proof-suggestion
created: 2026-06-14
```
