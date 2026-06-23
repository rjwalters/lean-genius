# Problem: Besicovitch's Theorem — ℚ-Linear Independence of Square Roots of Squarefree Integers

**Slug**: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-02
**Created**: 2026-06-14
**Status**: Active
**Source**: gallery-gap <!-- open question extending sqrt2-plus-sqrt3-plus-sqrt5-irrational -->

## Problem Statement

### Formal Statement

$$
\text{For distinct squarefree integers } a_1,\dots,a_n > 1,\ \{1, \sqrt{a_1}, \dots, \sqrt{a_n}\} \text{ is linearly independent over } \mathbb{Q}.
$$

Besicovitch (1940): if $a_1,\dots,a_n$ are distinct squarefree positive integers then $\sqrt{a_1},\dots,\sqrt{a_n}$ are linearly independent over $\mathbb{Q}$; more strongly, the family of squarefree-product radicals forms a $\mathbb{Q}$-basis of the multiquadratic field they generate.

### Plain Language

The gallery proof shows the specific number $\sqrt2 + \sqrt3 + \sqrt5$ is irrational. This open question asks for the general structural theorem behind it: there is never a nontrivial rational relation among the square roots of distinct squarefree integers. So $\sqrt2,\sqrt3,\sqrt5,\sqrt6,\sqrt7,\dots$ are "independent" over $\mathbb{Q}$ — no rational combination collapses to a rational number unless every coefficient is zero.

### Why This Matters

This is the reusable engine behind a whole family of irrationality results. It generalizes the ad-hoc $\sqrt2+\sqrt3+\sqrt5$ argument to arbitrary finite sets and characterizes the structure of the multiquadratic field $\mathbb{Q}(\sqrt{a_1},\dots,\sqrt{a_n})$, which has degree $2^n$ over $\mathbb{Q}$ with Galois group $(\mathbb{Z}/2)^n$. It is **not** currently in Mathlib v4.26.0.

## Known Results

### What's Already Proven

- Irrationality of $\sqrt2 + \sqrt3 + \sqrt5$ — gallery proof `sqrt2-plus-sqrt3-plus-sqrt5-irrational`
- `Nat.Prime.irrational_sqrt`, `irrational_nrt_of_notint_nrt` — Mathlib (single square roots)
- Multiquadratic field has degree $2^n$, Galois group $(\mathbb{Z}/2)^n$ — classical

### What's Still Open (in Lean)

- A structured induction on $n$ proving full $\mathbb{Q}$-linear independence
- Key step: $\sqrt{a_{n+1}} \notin \mathbb{Q}(\sqrt{a_1},\dots,\sqrt{a_n})$ for $a_{n+1}$ squarefree, not a square-class product of earlier radicals

### Our Goal

Formalize Besicovitch's general theorem. A clean intermediate target is the prime case ($a_i$ distinct primes), where the field-degree argument is sharpest, then extend to general squarefree integers via prime factorizations.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sqrt2-plus-sqrt3-plus-sqrt5-irrational | Direct $n=3$, $\{2,3,5\}$ instance | Conjugation / minimal polynomial |
| nth-root-irrational | Single-radical irrationality | Rational-root / valuation |

## Initial Thoughts

### Potential Approaches

1. **Field-theoretic induction on the quadratic tower** (recommended): show $[\mathbb{Q}(\sqrt{a_1},\dots,\sqrt{a_n}):\mathbb{Q}] = 2^n$ by proving each $\sqrt{a_{k+1}}$ has degree 2 over the previous field. Independence of the $2^n$ squarefree-product monomials follows from the basis structure.
   - Why it might work: matches Mathlib's `IntermediateField.adjoin` / `FiniteDimensional` API.
   - Risk: the "genuinely new radical" step needs a clean valuation or parity argument.

2. **Galois-action / conjugation**: the group $(\mathbb{Z}/2)^n$ acts by independent sign flips $\sqrt{a_i} \mapsto \pm\sqrt{a_i}$; a nontrivial rational relation fixed by all sign flips forces every coefficient to vanish.
   - Why it might work: conceptual, mirrors the $n=3$ gallery proof.
   - Risk: constructing and proving well-definedness of the automorphisms in Lean.

### Key Difficulties

- The inductive step (a new radical is not in the previous field) requires 2-adic valuation reasoning or multiplicativity of field degrees.
- General squarefree (vs. prime) integers add bookkeeping over shared prime factors.

### What Would a Proof Need?

- Key lemma 1: $\sqrt{m} \notin \mathbb{Q}(\sqrt{a_1},\dots,\sqrt{a_n})$ when $m$ is squarefree and not a square-class product of the $a_i$.
- Key lemma 2: degree multiplicativity in the quadratic tower (`IntermediateField.adjoin` + degrees).
- Technical requirements: `Mathlib.FieldTheory.*`, `Irrational`, `Nat.Squarefree`, `Nat.factorization`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classical theorem with several elementary proofs.
- Mathlib has strong field-theory and squarefree-number support, but this theorem is absent.
- The induction is conceptually clear; the labor is the Lean-mechanical "new radical" step.

**Estimated Effort**:
- Exploration: 1–2 days (survey Mathlib field-tower API)
- If tractable: 1–2 weeks for the prime case; more for general squarefree

## References

### Papers
- A. S. Besicovitch, "On the linear independence of fractional powers of integers", J. London Math. Soc. 15 (1940), 3–6.
- I. Richards, "An application of Galois theory to elementary arithmetic", Adv. Math. 13 (1974).

### Mathlib
- `Mathlib.FieldTheory.Adjoin` — `IntermediateField.adjoin`, degrees of adjoined elements
- `Nat.Squarefree`, `Nat.factorization` — squarefree structure
- `Irrational` — irrationality primitives

## Metadata

```yaml
tags:
  - number-theory
  - field-theory
  - linear-independence
  - irrationality
  - besicovitch
related_proofs:
  - sqrt2-plus-sqrt3-plus-sqrt5-irrational
  - nth-root-irrational
difficulty: medium
source: gallery-gap
created: 2026-06-14
```
