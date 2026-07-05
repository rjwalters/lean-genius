# Problem: Congruence Restrictions on Prime Factors of Mersenne Numbers

**Slug**: mersenne-prime-exponent-oq-02
**Created**: 2026-07-05T03:14:24-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a prime $p$ and any prime $q$ dividing the Mersenne number $M_p = 2^{p} - 1$:

$$
q \equiv 1 \pmod{2p} \qquad\text{and}\qquad q \equiv \pm 1 \pmod{8}.
$$

The first congruence follows because the order of $2$ in $(\mathbb{Z}/q\mathbb{Z})^{\times}$ is
exactly $p$ (it divides $p$ since $2^{p}\equiv 1$, and is not $1$), so $p \mid q - 1$ by Fermat's
little theorem; combined with $q$ odd this gives $2p \mid q-1$. The second congruence is the
statement that $2$ is a quadratic residue mod $q$ (since $2 \equiv 2^{p+1} = (2^{(p+1)/2})^2$ when
$p$ is odd), which by the supplement to quadratic reciprocity holds iff $q \equiv \pm 1 \pmod 8$.

### Plain Language

Every prime factor of a Mersenne number $2^{p}-1$ is highly constrained: it must be one more than a
multiple of $2p$, and must land in the residue classes $\pm 1$ modulo $8$. These are the classical
trial-division shortcuts (Euler, Lagrange) that make Mersenne primality testing feasible — e.g. a
factor of $2^{11}-1 = 2047$ must be $\equiv 1 \pmod{22}$, immediately singling out $23$.

### Why This Matters

This strengthens the parent result (`mersenne-prime-exponent`, which shows $p$ must be prime) from
a statement about the *exponent* to a statement about the *factors*. It is the theoretical engine
behind efficient Mersenne factor search and a clean showcase of multiplicative order plus the
quadratic-reciprocity supplement working together — both well supported in Mathlib.

## Known Results

### What's Already Proven

- `mersenne-prime-exponent` (gallery) — $2^{p}-1$ prime $\implies p$ prime.
- Mathlib: `ZMod.orderOf`, `orderOf_dvd_of_pow_eq_one`, `ZMod.pow_card_sub_one_eq_one`
  (Fermat's little theorem), and `ZMod.exists_sq_eq_two_iff` (the mod-8 residue criterion for
  $2$ being a QR).

### What's Still Open

- Packaging the order argument and the QR supplement into a single reusable Lean lemma about
  Mersenne factors.

### Our Goal

Formalise both congruences for an arbitrary prime factor $q \mid 2^{p}-1$ (with $p$ an odd prime),
with `0` sorries and `0` axioms, reusing Mathlib's order and quadratic-residue API.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| mersenne-prime-exponent | Parent problem; same Mersenne setting | multiplicative order, Fermat's little theorem |
| quadratic-reciprocity (if present) | Supplies the $\pm 1 \pmod 8$ criterion | Legendre symbol supplement |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Order-of-2 argument for $q \equiv 1 \pmod{2p}$.
   - Why it might work: `orderOf (2 : ZMod q)` divides $p$ (prime) and is $\ne 1$, so equals $p$;
     then `orderOf_dvd_card_sub_one` / FLT gives $p \mid q-1$, and oddness of $q$ upgrades to $2p$.
   - Risk: Handling the `2 ≠ 0 in ZMod q` and `q ≠ 2` side conditions cleanly.

2. **Approach B**: Quadratic-residue route for $q \equiv \pm 1 \pmod 8$.
   - Why it might work: $2^{p} \equiv 1$ with $p$ odd gives $2 \equiv (2^{(p+1)/2})^{2}$, so $2$ is a
     QR mod $q$; `ZMod.exists_sq_eq_two_iff` then yields the mod-8 condition.
   - Risk: Aligning Mathlib's exact form of the "$2$ is a square" iff statement with the residue
     classes $\pm 1 \pmod 8$.

### Key Difficulties

- Two independent number-theoretic facts must be combined; each needs its Mathlib lemma located and
  its hypotheses discharged.
- Care with the parity/oddness bookkeeping to get $2p$ (not just $p$) dividing $q-1$.

### What Would a Proof Need?

- Key lemma 1: `orderOf (2 : ZMod q) = p` from $2^{p} \equiv 1$ and $p$ prime.
- Key lemma 2: $2$ is a quadratic residue mod $q$ $\iff$ $q \equiv \pm 1 \pmod 8$
  (Mathlib `ZMod.exists_sq_eq_two_iff`).
- Technical requirements: `ZMod`, `orderOf`, FLT, the QR supplement.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Both halves are standard undergraduate number theory with direct Mathlib support.
- The parent Mersenne exponent result establishes the surrounding infrastructure.
- Main effort is lemma-plumbing rather than new mathematics.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days
- If hard: up to a week if the QR supplement needs adaptation

## References

### Papers
- L. Euler / J.-L. Lagrange — classical results on factors of $2^{p}-1$.

### Online Resources
- https://en.wikipedia.org/wiki/Mersenne_prime#Theorems_about_Mersenne_numbers — the two congruence theorems.

### Mathlib
- `Mathlib.FieldTheory.Finite.Basic` — `orderOf` in finite fields, FLT.
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` — `ZMod.exists_sq_eq_two_iff`.
- `Mathlib.Data.ZMod.Basic` — modular arithmetic scaffolding.

## Metadata

```yaml
tags:
  - number-theory
  - mersenne
  - quadratic-reciprocity
related_proofs:
  - mersenne-prime-exponent
difficulty: medium
source: proof-suggestion
created: 2026-07-05T03:14:24-07:00
```
