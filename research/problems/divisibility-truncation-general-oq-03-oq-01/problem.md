# Problem: Base-b divisibility osculators — d | b·c − 1 for any base b coprime to d

**Slug**: divisibility-truncation-general-oq-03-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For integers $d \ge 1$ and base $b$ with $\gcd(b, d) = 1$, there exists an **osculator** $c$ with
$$
d \mid b\,c - 1,
$$
i.e. $b\,c \equiv 1 \pmod d$, and $c$ is canonically given by a Bézout coefficient of $\gcd(b,d) = 1$. The classical decimal case ($b = 10$) is the special case.

### Plain Language

Osculators are the multipliers behind quick divisibility tests. The parent entry shows that Bézout coefficients are the canonical osculators for the base-$10$ situation. This leaf generalizes to an **arbitrary base** $b$ coprime to $d$: the same Bézout argument produces $c$ with $b\,c \equiv 1 \pmod d$. So every base coprime to $d$ admits an osculator, and it is exactly the modular inverse of $b$ mod $d$.

### Why This Matters

Unifies base-specific divisibility-test folklore into one clean statement: an osculator is just a modular inverse, which exists precisely when the base is coprime to the modulus. Reusable for general-base digit/divisibility formalizations.

## Known Results

### What's Already Proven

- Parent `divisibility-truncation-general-oq-03` — Bézout coefficients are canonical osculators (base-10 framing).
- Mathlib: `Nat.gcd`/`Int.gcd` Bézout (`Nat.gcdA`/`gcdB`, `Int.gcd_eq_gcd_ab`), `ZMod.inv`, `Nat.Coprime` and existence of modular inverses (`ZMod.unitOfCoprime`, `Nat.Coprime` ↔ unit in `ZMod d`).

### What's Still Open

- The base-$b$ existence statement as a named theorem.
- Identifying $c$ canonically with the Bézout coefficient / `ZMod` inverse.

### Our Goal

Prove existence (and the canonical Bézout/`ZMod`-inverse characterization) of the base-$b$ osculator for any $b$ coprime to $d$, axiom-free.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| divisibility-truncation-general-oq-03 | Parent: canonical osculators via Bézout | Bézout coefficients |
| divisibility-truncation-general-oq-01 | Truncation/divisibility framework | modular arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Approach A — `ZMod d` units**: $\gcd(b,d)=1$ makes $b$ a unit in `ZMod d` (`ZMod.unitOfCoprime`); take $c$ as its inverse, so $b c = 1$ in `ZMod d`, i.e. $d \mid bc - 1$.
   - Why it might work: shortest path; existence is immediate from coprimality.
   - Risk: bridging `ZMod` equality back to the $\mathbb{Z}$ divisibility statement (`ZMod.intCast_zmod_eq_zero_iff_dvd`).

2. **Approach B — explicit Bézout**: Use $\gcd(b,d) = 1 = b\,u + d\,v$ so $c = u$ satisfies $bc - 1 = -dv$, divisible by $d$.
   - Why it might work: matches the parent's "Bézout coefficient is the osculator" framing directly.
   - Risk: sign/`Int` vs `Nat` bookkeeping.

### Key Difficulties

- Translating between `ZMod` inverse and integer divisibility.
- Stating canonicity (which representative of $c$ mod $d$).

### What Would a Proof Need?

- Key lemma 1: coprimality ⟹ $b$ is a unit mod $d$ (or Bézout identity).
- Key lemma 2: `ZMod`/divisibility bridge.
- Technical requirements: `Nat.Coprime`, `ZMod.unitOfCoprime`, `Int.gcd_eq_gcd_ab`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Existence of a modular inverse from coprimality is a one-liner in Mathlib.
- The parent already provides the Bézout-osculator viewpoint to mirror.
- Only the `ZMod` ↔ divisibility translation needs care.

**Estimated Effort**:
- Exploration: 1–2 hours
- If tractable: under 1 day
- If hard: unknown (unlikely)

## References

### Mathlib
- `Mathlib.Data.ZMod.Basic` — `ZMod.unitOfCoprime`, `ZMod.intCast_zmod_eq_zero_iff_dvd`.
- `Mathlib.RingTheory.Int.Basic` / `Mathlib.Data.Int.GCD` — Bézout (`Int.gcd_eq_gcd_ab`).

## Metadata

```yaml
tags:
  - number-theory
  - divisibility
  - euclidean-algorithm
  - modular-arithmetic
related_proofs:
  - divisibility-truncation-general-oq-03
  - divisibility-truncation-general-oq-01
difficulty: low
source: gallery-gap
created: 2026-06-24
```
