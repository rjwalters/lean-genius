# Problem: Exponent-gcd image of the power map on a finite commutative monoid

**Slug**: cauchy-group-theorem-oq-01-oq-01-oq-01-oq-01-oq-03-oq-02-oq-01-oq-02
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a finite commutative group $G$ with exponent $e = \exp G$, the parent established
$$
\operatorname{range}(x \mapsto x^n) = \operatorname{range}\!\big(x \mapsto x^{\gcd(n,\,e)}\big).
$$
Extend this to a finite commutative **monoid** $M$: identify the correct exponent-gcd statement for the image of the power map when $x^{\exp M} = 1$ fails on non-units — e.g. the equality restricted to the group of units $M^\times$, or a corrected statement on all of $M$.

### Plain Language

On a finite abelian group, raising to the $n$-th power has the same image as raising to the $\gcd(n, \exp G)$-th power, because Bézout lets you realize the gcd exponent from $n$ and the exponent. In a monoid, non-invertible elements need not satisfy $x^{\exp M} = 1$, so the clean group statement breaks. This problem finds and proves the right generalization — most plausibly the identity holds verbatim on the unit group $M^\times$, with a separately characterized behavior on non-units.

### Why This Matters

The power map's image controls $n$-th-power residues and surjectivity of $x \mapsto x^n$. Pinning down exactly how the group-theoretic exponent-gcd law degrades in the monoid setting is a clean structural question that sharpens the parent result and clarifies the role of invertibility.

### What's Already Proven

- Group case: $\operatorname{range}(x^n) = \operatorname{range}(x^{\gcd(n,\exp G)})$ (parent), via Bézout on exponents.
- $x^{\exp G} = 1$ for all $x$ in a finite group (order divides exponent).

### What's Still Open

- The correct image statement on a finite commutative monoid.
- Whether restricting to $M^\times$ recovers the group identity, and what the non-unit part contributes.

### Our Goal

Prove that for finite commutative $M$, $\operatorname{range}(x \mapsto x^n)$ restricted to $M^\times$ equals $\operatorname{range}(x \mapsto x^{\gcd(n,\exp M^\times)})$ on $M^\times$; and give a counterexample or corrected description for the non-unit part.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-group-theorem power-map line (parent) | direct predecessor | Bézout, exponent, image of power map |
| bezout-identity | gcd realized as an integer combination | Bézout's identity |

## Initial Thoughts

### Potential Approaches

1. **Restrict to the unit group**: $M^\times$ is a finite abelian group, so the parent theorem applies verbatim; then analyze $M \setminus M^\times$ separately.
   - Why it might work: reduces to a solved case on the invertible part.
   - Risk: characterizing the non-unit image may be genuinely subtle (idempotents, nilpotents).

2. **Idempotent decomposition**: a finite commutative monoid decomposes over its idempotents; handle each archimedean component.
   - Why it might work: structure theory pins the power map on each piece.
   - Risk: Mathlib support for finite-monoid structure theory is limited.

### Key Difficulties

- No global $x^{\exp M} = 1$; the gcd/Bézout trick needs invertibility.
- Deciding the cleanest true statement to formalize (units-only vs. full corrected form).

### What Would a Proof Need?

- Key lemma 1: parent exponent-gcd law on the finite abelian group $M^\times$.
- Key lemma 2: a characterization or counterexample for non-units.
- Technical requirements: `Monoid`, `IsUnit`, `Units`, `Monoid.exponent`, `Nat.gcd`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The units-only statement is a near-direct corollary of the parent applied to $M^\times$.
- The genuinely new content (non-unit behavior) is bounded and may resolve to a crisp counterexample.
- Mathlib has `Monoid.exponent`, `Units`, and the Bézout API.

**Estimated Effort**:
- Exploration: 1 day
- If tractable (units case): 2–4 days
- If hard (full non-unit theory): 1 week

## References

### Papers
- Clifford & Preston, The Algebraic Theory of Semigroups (1961) — finite commutative monoid structure.

### Online Resources
- https://en.wikipedia.org/wiki/Exponent_(group_theory) — exponent and power maps.

### Mathlib
- `Mathlib.GroupTheory.Exponent` — `Monoid.exponent`.
- `Mathlib.Algebra.Group.Units` — the unit group `Mˣ`.

## Metadata

```yaml
tags:
  - algebra
  - group-theory
  - finite-groups
  - power-map
  - monoid-exponent
  - gcd
related_proofs:
  - cauchy-group-theorem
  - bezout-identity
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 5/10
**Tractability**: 6/10
