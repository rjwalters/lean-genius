# Problem: Complete Quantitative Bounds for Roth's Theorem

**Slug**: roth-theorem-k3-oq-01-wip-01
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
r_3(N) = \max\{ |A| : A \subseteq [N],\ A \text{ contains no 3-term arithmetic progression}\},
\qquad r_3(N) = o(N),
$$
with quantitative upper bounds from Roth (1953) through Kelley–Meka (2023).

### Plain Language

The Roth number r_3(N) is the largest possible size of a subset of {1,...,N} that
contains no three-term arithmetic progression (no x, x+d, x+2d all in the set).
Roth's theorem says this is a vanishing fraction of N as N grows. This problem is
about formalizing r_3(N) and the chain of quantitative upper bounds on it, from
Roth's original density-increment bound to modern (Kelley–Meka) results.

### Why This Matters

Roth's theorem is the base case of Szemerédi's theorem and a cornerstone of additive
combinatorics. A formalized definition of r_3(N) with even a weak explicit bound
gives a foundation the gallery can extend toward stronger density-increment and
Fourier-analytic arguments.

## Known Results

### What's Already Proven

- The source entry `roth-theorem-k3-oq-01` defines r_3(N) and states the major bounds.
- Basic monotonicity / threshold structure of Roth numbers exists in the gallery
  (see erdos-3 Roth-number work).

### What's Still Open

- Formal proof of a quantitative upper bound r_3(N) = O(N / (log N)^c) for explicit c.
- The full Kelley–Meka-strength bound is far out of reach for now.

### Our Goal

Complete the work-in-progress source proof `roth-theorem-k3-oq-01`: discharge the
remaining `sorry`s, prioritizing the definitional lemmas and the weakest non-trivial
density bound (e.g. a clean density-increment step) rather than the strongest known
result.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| roth-theorem-k3-oq-01 | Direct parent WIP proof being completed | Roth number, 3-AP-free sets |
| erdos-3-incomplete-01 | Roth-number monotonicity / downward-closure | thresholds, monotonicity |
| szemeredi-* | Higher-k generalization context | density increment |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Formalize the density-increment iteration (Roth 1953).
   - Why it might work: Elementary Fourier + pigeonhole; classical and well-documented.
   - Risk: The Fourier-on-Z/N infrastructure may be thin in Mathlib.

2. **Approach B**: Establish only the definitional API + a combinatorial bound.
   - Why it might work: Gets a machine-checked non-trivial statement quickly.
   - Risk: Weaker headline result.

### Key Difficulties

- Fourier analysis on Z/NZ formalization overhead.
- Turning the density-increment recursion into a clean induction.

### What Would a Proof Need?

- Key lemma 1: A precise definition and basic bounds for r_3(N).
- Key lemma 2: A density-increment or counting step giving o(N).
- Technical requirements: Finite-field / cyclic-group Fourier or a counting argument.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Definitional and monotonicity parts are tractable now.
- A genuine quantitative bound requires nontrivial additive-combinatorics machinery.
- Related gallery work (erdos-3 Roth numbers) provides reusable pieces.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 1-2 weeks (weak bound)
- If hard: unknown (strong bounds)

## References

### Papers
- K. Roth, "On certain sets of integers", 1953 — original density-increment bound.
- Kelley–Meka, "Strong bounds for 3-progressions", 2023 — state of the art.

### Online Resources
- Standard additive-combinatorics lecture notes on Roth's theorem.

### Mathlib
- `Mathlib.Combinatorics.Additive.*` — additive combinatorics primitives.
- `Mathlib.Analysis.Fourier.*` — Fourier tools where applicable.

## Metadata

```yaml
tags:
  - combinatorics
  - additive-combinatorics
  - arithmetic-progressions
  - roth-number
  - szemeredi
related_proofs:
  - roth-theorem-k3-oq-01
  - erdos-3-incomplete-01
difficulty: high
source: gallery-gap
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 6/10
