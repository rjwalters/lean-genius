# Problem: Divisibility & Congruence for Generalized r-Derangement Numbers

**Slug**: derangements-convergence-oq-04-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $D_r(n)$ denote the number of $r$-derangements (permutations of $[n]$ avoiding a fixed cycle structure / with a prescribed forbidden-fixed-set of size $r$). Determine and prove the analogue of the classical identities

$$
(n-1) \mid D(n), \qquad D(n) \equiv (-1)^n \pmod{n-1},
$$

for $D_r(n)$: i.e. which divisibility relation $f(n,r) \mid D_r(n)$ and which congruence $D_r(n) \equiv g(n,r)$ hold.

### Plain Language

The parent proof `derangements-convergence-oq-04` establishes $(n-1) \mid D(n)$ for ordinary derangement numbers $D(n) = n!\sum_{k=0}^n \frac{(-1)^k}{k!}$. This problem asks whether an analogous divisibility or sign-congruence survives for the **generalized ($r$-)derangement numbers**, which count permutations avoiding a fixed cycle structure. The recurrence $D(n) = (n-1)(D(n-1) + D(n-2))$ is the engine behind the classical result; the task is to find and formalize the corresponding recurrence-driven identity for $D_r(n)$.

### Why This Matters

Derangement congruences are a clean testbed for formalizing integer recurrences and modular arithmetic in Lean. Generalizing to $r$-derangements connects to rencontres numbers and the combinatorics of restricted permutations — an area where Mathlib has `Nat.derangements` but little on the generalized family.

## Known Results

### What's Already Proven
- $(n-1) \mid D(n)$ and the recurrence $D(n)=(n-1)(D(n-1)+D(n-2))$ — gallery `derangements-convergence-oq-04`.
- `Nat.derangements` cardinality and basic recurrences — Mathlib.

### What's Still Open (for formalization)
- Identifying the correct $r$-derangement recurrence.
- The divisibility/congruence analogue for $D_r(n)$.

### Our Goal
Fix a precise definition of $D_r(n)$ (e.g. permutations with exactly the first $r$ points forbidden as fixed points, or the two-variable rencontres numbers), derive its recurrence, and prove the resulting divisibility/congruence.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| derangements-convergence-oq-04 | Direct parent; $r=$ all case | Recurrence, induction |
| derangements-convergence | Base derangement asymptotics | Inclusion-exclusion |

## Initial Thoughts

### Potential Approaches
1. **Recurrence + induction**: establish $D_r(n) = (n-1)(D_r(n-1)+D_r(n-2)) + (\text{correction})$ and push the divisibility through by induction, mirroring the parent.
2. **Inclusion–exclusion closed form**: derive $D_r(n)$ as a signed sum and read off the congruence via a telescoping/valuation argument.

### Key Difficulties
- Choosing the "right" generalization ($r$-derangements are defined several inequivalent ways in the literature); pick the one with the cleanest identity.
- The correction term may break simple $(n-1)$-divisibility, requiring a modified modulus.

### What Would a Proof Need?
- A clean recurrence for $D_r(n)$.
- An inductive divisibility/congruence lemma.

## Tractability Assessment

**Difficulty**: Medium

**Justification**: Self-contained combinatorial number theory reducible to integer recurrences; the main risk is definitional (selecting the generalization that admits a clean theorem).

## References

### Texts
- Stanley, *Enumerative Combinatorics* I (rencontres numbers).

### Mathlib
- `Nat.derangements`, `Finset.sum`, `Int.ModEq`, induction on recurrences.

## Metadata

```yaml
tags:
  - combinatorics
  - derangements
  - divisibility
  - congruence
related_proofs:
  - derangements-convergence-oq-04
  - derangements-convergence
difficulty: medium
source: gallery-gap
created: 2026-07-04
```
