# Problem: Fermat Prime Exponent Must Be a Power of Two

**Slug**: mersenne-prime-exponent-oq-01
**Created**: 2026-07-05T03:14:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall n \in \mathbb{N},\ n \ge 1,\quad \bigl(2^{n} + 1 \text{ is prime}\bigr) \implies \exists k \in \mathbb{N},\ n = 2^{k}.
$$

The proof mirrors the Mersenne exponent lemma (`mersenne-prime-exponent`): if $n$ has an
**odd** divisor $d > 1$, write $n = d\,m$. Then the algebraic factorisation

$$
2^{m} + 1 \ \bigm|\ (2^{m})^{d} + 1 = 2^{n} + 1 \qquad (d \text{ odd})
$$

exhibits a nontrivial factor $2^{m}+1$ with $1 < 2^{m}+1 < 2^{n}+1$, contradicting primality.
Hence $n$ has no odd divisor $> 1$, i.e. $n$ is a power of two.

### Plain Language

For a number of the form $2^{n}+1$ to be prime (a *Fermat prime*, such as $3, 5, 17, 257, 65537$),
the exponent $n$ is forced to be a power of two. This is the exact dual of the Mersenne fact that
$2^{p}-1$ prime forces $p$ prime: here the obstruction is an **odd** divisor of the exponent rather
than a proper divisor, and it is powered by the *sum*-of-powers factorisation $x^{d}+1 = (x+1)(x^{d-1}-x^{d-2}+\cdots+1)$ valid for odd $d$.

### Why This Matters

Fermat primes govern which regular $n$-gons are constructible with straightedge and compass
(Gauss–Wantzel: a regular $n$-gon is constructible iff $n$ is a power of two times a product of
distinct Fermat primes). Pinning the exponent to a power of two is the first structural
restriction and reuses exactly the exponent-divisibility lift already formalised for Mersenne
numbers, so it is a natural, self-contained companion result.

## Known Results

### What's Already Proven

- `mersenne-prime-exponent` (gallery) — $2^{p}-1$ prime $\implies p$ prime, via the
  difference-of-powers divisibility $2^{d}-1 \mid 2^{n}-1$ for $d \mid n$.
- `Nat.sub_one_dvd_sub_of_dvd_sub` / geometric-sum factorisations in Mathlib.

### What's Still Open

- The clean formalisation of the *sum*-of-powers direction ($2^{m}+1 \mid 2^{dm}+1$ for odd $d$).
- Wiring this into the constructible-polygon (Gauss–Wantzel) narrative.

### Our Goal

Prove the single implication "$2^{n}+1$ prime $\implies n$ is a power of two" in Lean 4, reusing
the odd-divisor obstruction, with `0` sorries and `0` axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| mersenne-prime-exponent | Dual result; same exponent-divisibility lift | odd/proper-divisor obstruction, `Nat.dvd` factorisation |
| infinitude-of-primes | Ambient prime-divisibility toolkit | `Nat.Prime`, minimal factor |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Contrapositive via odd-divisor extraction.
   - Why it might work: If $n$ is not a power of two, `Nat.ord_compl`/`Nat.factorization 2 n`
     yields an odd divisor $d > 1$; the sum-of-powers factorisation gives the nontrivial factor.
   - Risk: The identity $2^{m}+1 \mid 2^{dm}+1$ for odd $d$ may need a bespoke induction; Mathlib
     may only have the difference version directly.

2. **Approach B**: Work in `ZMod (2^m + 1)` and evaluate $2^{n} \equiv (-1)^{d} = -1$.
   - Why it might work: $2^{m} \equiv -1 \pmod{2^{m}+1}$, so $2^{n} = (2^{m})^{d} \equiv (-1)^{d} = -1$,
     giving $2^{n}+1 \equiv 0$. Clean modular argument avoiding explicit polynomial identities.
   - Risk: Bounding $1 < 2^{m}+1 < 2^{n}+1$ to conclude a *proper* factor still needs care.

### Key Difficulties

- Establishing the odd-exponent sum-of-powers divisibility cleanly in `Nat` (sign issues push
  toward a `ZMod` or `Int` argument).
- Extracting an odd divisor $> 1$ from "$n$ is not a power of two" via the 2-adic valuation.

### What Would a Proof Need?

- Key lemma 1: for odd $d$, $2^{m}+1 \mid 2^{dm}+1$ (or the `ZMod` congruence $2^{n} \equiv -1$).
- Key lemma 2: $n$ not a power of two $\iff$ $n$ has an odd divisor $> 1$ (2-adic valuation).
- Technical requirements: `Nat.factorization`, `ZMod`, `Nat.Prime.eq_one_of_self_dvd`-style bounds.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The dual Mersenne result is already formalised in the gallery; this reuses the same skeleton.
- The `ZMod (2^m+1)` route is short and idiomatic in Mathlib.
- Only obstruction is the odd-power sign, which `Odd.neg_one_pow` handles directly.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days
- If hard: unlikely to exceed a week

## References

### Papers
- C. F. Gauss, *Disquisitiones Arithmeticae*, 1801 — constructible polygons and Fermat primes.

### Online Resources
- https://en.wikipedia.org/wiki/Fermat_number — statement and elementary proof of the exponent restriction.

### Mathlib
- `Mathlib.NumberTheory.LucasLehmer` — Mersenne-number infrastructure and `mersenne` API.
- `Mathlib.Data.ZMod.Basic` — modular-arithmetic evaluation for Approach B.
- `Mathlib.Algebra.GeomSum` — geometric-sum / sum-of-powers factorisations.

## Metadata

```yaml
tags:
  - number-theory
  - fermat-prime
  - divisibility
related_proofs:
  - mersenne-prime-exponent
  - infinitude-of-primes
difficulty: medium
source: proof-suggestion
created: 2026-07-05T03:14:19-07:00
```
