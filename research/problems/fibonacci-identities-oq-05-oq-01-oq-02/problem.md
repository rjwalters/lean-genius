# Problem: Weighted product-sum identities for Lucas and Gibonacci sequences

**Slug**: fibonacci-identities-oq-05-oq-01-oq-02
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\sum_{k=1}^{n} k\, L_k L_{k+1} \;=\; ?\qquad\text{and more generally}\qquad
\sum_{k=1}^{n} k\, G_k G_{k+1}\;=\;\text{(closed form)},
$$
where $L_k$ are the Lucas numbers ($L_0=2,\,L_1=1$) and $G_k$ is a general Gibonacci
sequence ($G_0=a,\,G_1=b,\,G_{k+1}=G_k+G_{k-1}$). The parity/Cassini correction term
$(-1)^k$ appearing in the Fibonacci case should be replaced by the sequence discriminant
$b^2-ab-a^2$.

### Plain Language

The gallery proof `fibonacci-identities-oq-05-oq-01` establishes a closed form for the
weighted product-sum $\sum_{k} k\,F_k F_{k+1}$ of consecutive Fibonacci numbers. This
problem generalizes that identity in two directions: (1) to the Lucas numbers, and
(2) to arbitrary Gibonacci sequences (same recurrence, arbitrary initial conditions).
The goal is to identify how the Cassini-type parity correction $(-1)^k$ transforms into
the sequence discriminant under generalization, and to prove the resulting closed forms.

### Why This Matters

Product-sum identities are a testbed for telescoping and induction machinery over
integer sequences. Unifying the Fibonacci, Lucas, and Gibonacci cases into a single
discriminant-parameterized identity clarifies which algebraic invariant drives the
correction term, and produces reusable Mathlib-style lemmas for the whole Gibonacci
family rather than one-off Fibonacci facts.

## Known Results

### What's Already Proven

- `fib_weighted_prod_sum`: closed form for $\sum_{k} k\,F_k F_{k+1}$ — proven in
  gallery proof `fibonacci-identities-oq-05-oq-01`.
- Cassini/Catalan identities for Fibonacci and Lucas numbers (standard; Mathlib has
  `Nat.fib` lemmas, Lucas numbers may need scaffolding).

### What's Still Open

- The Lucas analogue $\sum_{k} k\,L_k L_{k+1}$ in closed form.
- The general Gibonacci identity with the discriminant $b^2-ab-a^2$ as correction.
- A single unified statement specializing to all three via the discriminant.

### Our Goal

Prove the Lucas weighted product-sum identity first (concrete, closed form), then
lift to the Gibonacci family, showing the parity correction becomes the discriminant.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fibonacci-identities-oq-05-oq-01 | Direct parent — the Fibonacci case to generalize | telescoping, weighted-sum induction |
| fibonacci-identities | Base Cassini/product identities | induction on sequence index |

## Initial Thoughts

### Potential Approaches

1. **Approach A — direct telescoping with a summation-by-parts (Abel) transform**:
   Rewrite $k\,G_k G_{k+1}$ as a discrete derivative of a product plus a correction,
   then telescope.
   - Why it might work: the Fibonacci case already yields to this; the correction is
     the only piece that changes.
   - Risk: bookkeeping of the discriminant term across arbitrary initial conditions.

2. **Approach B — Binet-form / matrix-power computation**:
   Express $G_k$ via the golden-ratio closed form and evaluate the sum symbolically.
   - Why it might work: makes the discriminant appear explicitly as $b^2-ab-a^2$.
   - Risk: irrational-arithmetic formalization overhead in Lean.

### Key Difficulties

- Lucas numbers are not directly in Mathlib as a named sequence; may need a definition.
- Tracking the sign/parity correction cleanly as a discriminant across the family.

### What Would a Proof Need?

- Key lemma 1: a Gibonacci Cassini identity $G_{k-1}G_{k+1}-G_k^2 = (-1)^k(b^2-ab-a^2)$.
- Key lemma 2: weighted-sum telescoping lemma generic over the recurrence.
- Technical requirements: a clean Gibonacci definition and its basic recurrence lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The Fibonacci case is already formalized; this is a structured generalization.
- Telescoping/induction over integer sequences is well-supported in Mathlib.
- Main new work is a Gibonacci Cassini identity and careful discriminant tracking.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: several days for the Lucas + Gibonacci identities
- If hard: irrational Binet route could balloon

## References

### Papers
- Vajda, *Fibonacci & Lucas Numbers, and the Golden Section* (1989) — product-sum identities.

### Online Resources
- OEIS A000032 (Lucas numbers) — sequence values and identities.

### Mathlib
- `Mathlib.Combinatorics.Fibonacci` / `Nat.fib` — Fibonacci scaffolding to mirror.
- `Finset.sum` telescoping lemmas — `Finset.sum_range_succ`, Abel summation.

## Metadata

```yaml
tags:
  - number-theory
  - fibonacci
  - lucas
  - gibonacci
  - summation-identity
related_proofs:
  - fibonacci-identities-oq-05-oq-01
  - fibonacci-identities
difficulty: medium
source: gallery-gap
created: 2026-07-04
```

**Significance**: 5/10
**Tractability**: 6/10
