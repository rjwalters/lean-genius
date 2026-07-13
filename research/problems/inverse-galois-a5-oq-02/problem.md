# Problem: Realize PSL(2,7) (order 168) as a Galois Group over ℚ

**Slug**: inverse-galois-a5-oq-02
**Created**: 2026-06-14
**Status**: Active
**Source**: gallery-gap <!-- open question extending inverse-galois-a5 -->

## Problem Statement

### Formal Statement

$$
\exists\, f \in \mathbb{Q}[x]\ \text{(explicit)}\ \text{with}\ \operatorname{Gal}(f/\mathbb{Q}) \cong \mathrm{PSL}(2,7) \cong \mathrm{GL}(3,2),\ |\mathrm{PSL}(2,7)| = 168.
$$

Extend the gallery's realization of $A_5$ (the first non-solvable Galois group) to the next simple non-solvable group, $\mathrm{PSL}(2,7)$, by exhibiting and verifying a concrete polynomial over $\mathbb{Q}$.

### Plain Language

The gallery proof `inverse-galois-a5` writes down an explicit degree-5 polynomial whose "symmetry group" (Galois group) is $A_5$ — the smallest non-solvable group, which is *why* the general quintic has no radical formula. This open question asks for the next landmark: produce a concrete polynomial over the rationals whose symmetry group is $\mathrm{PSL}(2,7)$, the simple group of order 168 (the second-smallest non-abelian simple group, famous as the automorphism group of the Klein quartic and of the Fano plane).

### Why This Matters

It is a concrete data point on the Inverse Galois Problem (which groups arise as $\operatorname{Gal}(\,\cdot\,/\mathbb{Q})$?), extending the gallery beyond $A_5$ to a second simple non-solvable group. $\mathrm{PSL}(2,7)$ is well understood and known to be realizable (it is a Galois group over $\mathbb{Q}$), so this is a *formalize-a-known-construction* task: choose an explicit septic (degree-7) polynomial with Galois group $\mathrm{PSL}(2,7)$ acting on the Fano-plane points and verify the group via resolvents / discriminant / cycle-type evidence.

## Known Results

### What's Already Proven

- $A_5$ realized over $\mathbb{Q}$ by an explicit quintic — gallery proof `inverse-galois-a5`
- Every solvable group is a Galois group over $\mathbb{Q}$ (Shafarevich) — classical, not in Mathlib
- $\mathrm{PSL}(2,7) \cong \mathrm{GL}(3,2)$ is simple of order 168 — classical; Mathlib has finite-group / `Equiv.Perm` machinery
- Standard explicit septics with group $\mathrm{PSL}(2,7)$ exist in the number-theory literature (e.g. Trinks' polynomial $x^7 - 7x + 3$)

### What's Still Open (in Lean)

- Any formalized realization beyond $A_5$ in this gallery
- Lean verification that a specific septic has Galois group exactly $\mathrm{PSL}(2,7)$ (order 168, transitive, contained in $A_7$ via square discriminant)

### Our Goal

Pick the standard polynomial $f(x) = x^7 - 7x + 3$ (Trinks, 1968; $\operatorname{Gal} = \mathrm{PSL}(2,7)$). Establish in Lean: (1) irreducibility over $\mathbb{Q}$ (transitivity, group order divisible by 7); (2) the discriminant is a perfect square (so $\operatorname{Gal} \le A_7$); (3) factorization cycle types modulo several primes pin the group to the order-168 subgroup $\mathrm{PSL}(2,7) \le A_7$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| inverse-galois-a5 | Template: explicit polynomial → non-solvable Galois group | Irreducibility, discriminant, cycle types |
| abel-ruffini-* | Non-solvability and Galois-group obstructions | Galois theory of the symmetric/alternating groups |
| solution-of-cubic / quartic | Resolvent technique for small-degree Galois groups | Resolvents |

## Initial Thoughts

### Potential Approaches

1. **Mod-p factorization (Dedekind) + discriminant** (recommended): irreducibility gives transitivity ($7 \mid |G|$); square discriminant gives $G \le A_7$; Frobenius cycle types from factorizations mod small primes force $G = \mathrm{PSL}(2,7)$ (the unique transitive order-168 subgroup of $A_7$).
   - Why it might work: each ingredient is computational and matches Mathlib's `Polynomial.Monic`, `ZMod` factorization, and discriminant tooling.
   - Risk: identifying the group from cycle-type data requires a transitive-subgroup classification argument that may need to be axiomatized or done by explicit group reasoning.

2. **Direct Galois-group computation via splitting field**: heavy; likely infeasible to fully mechanize without large group-theory development.

### Key Difficulties

- Pinning the group to exactly 168 (not all of $A_7$, order 2520) needs either a resolvent or a classification of transitive subgroups of $A_7$ of order 168.
- Computing discriminants and mod-$p$ factorizations cleanly in Lean.

### What Would a Proof Need?

- Key lemma 1: $x^7-7x+3$ irreducible over $\mathbb{Q}$ (e.g. mod-2 factorization or rational-root + further argument).
- Key lemma 2: $\operatorname{disc}(f)$ is a perfect square in $\mathbb{Q}$.
- Key lemma 3: enough Frobenius cycle types to exclude all transitive subgroups of $A_7$ except $\mathrm{PSL}(2,7)$.
- Technical requirements: `Mathlib.FieldTheory.Galois`, `Polynomial` discriminant, `ZMod` factorization, finite-group order facts.

## Tractability Assessment

**Difficulty**: Hard

**Justification**:
- The polynomial and its group are classical and well-documented, so the target is unambiguous.
- But fully certifying "Galois group = exactly PSL(2,7)" in Lean is substantial — the subgroup-pinning step is the main obstacle and may require a partial axiomatization of the transitive-subgroup classification (in line with the gallery's `axiomatized` policy for hard realizations).

**Estimated Effort**:
- Exploration: 2–3 days
- If tractable: several weeks; a staged result (irreducibility + square discriminant, with the order-168 pinning axiomatized) is a reasonable first deliverable.

## References

### Papers
- W. Trinks (1968), polynomial $x^7-7x+3$ with Galois group $\mathrm{PSL}(2,7)$.
- LMFDB, number field / Galois group tables for degree-7 fields.
- Serre, *Topics in Galois Theory* — realization of $\mathrm{PSL}(2,7)$ and rigidity.

### Mathlib
- `Mathlib.FieldTheory.Galois` — Galois group API
- `Mathlib.RingTheory.Polynomial.Discriminant` (or equivalent) — discriminant
- `ZMod` polynomial factorization — Dedekind / Frobenius cycle types

## Metadata

```yaml
tags:
  - galois-theory
  - inverse-galois-problem
  - psl27
  - non-solvable
  - polynomial-irreducibility
  - discriminant
related_proofs:
  - inverse-galois-a5
  - abel-ruffini-galois-extensions
difficulty: hard
source: gallery-gap
created: 2026-06-14
```
