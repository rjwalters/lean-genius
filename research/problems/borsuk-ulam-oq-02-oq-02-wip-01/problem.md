# Problem: Complete Equivariant Borsuk-Ulam for Compact Lie Groups

**Slug**: borsuk-ulam-oq-02-oq-02-wip-01
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{For a compact Lie group } G \text{ acting linearly on } V, W \text{ with } V^G = 0,\; \dim V > \dim W \implies \text{every } G\text{-equivariant map } f: S(V) \to W \text{ has a zero.}
$$

### Plain Language

The classical Borsuk-Ulam theorem says a continuous antipodal (Z/2-equivariant) map
from the n-sphere to R^n must send some point and its antipode to the same value.
This problem generalizes the statement to a general compact Lie group G (e.g. SO(n),
U(n)) acting on real representations V and W: when V has no nonzero G-fixed vectors
and dim V exceeds dim W, every G-equivariant map from the unit sphere of V into W
must vanish somewhere.

### Why This Matters

Equivariant Borsuk-Ulam theorems underpin many existence and non-embedding results
in equivariant topology and combinatorics. A machine-checked version for compact
Lie groups would provide a reusable infrastructure layer (representation spheres,
fixed-point subspaces, equivariant degree) that other formalized topology proofs can
build on.

## Known Results

### What's Already Proven

- Classical Z/2 Borsuk-Ulam is available in the gallery source-proof scaffolding.
- The source entry `borsuk-ulam-oq-02-oq-02` formalizes equivariant map definitions
  and fixed-point subspace properties (`V^G = 0`).

### What's Still Open

- The full equivariant existence-of-zero theorem for general compact Lie groups.
- Roughly ~2000 lines of supporting infrastructure (equivariant degree theory,
  representation-sphere machinery) identified as needed by the source survey.

### Our Goal

Complete the work-in-progress source proof `borsuk-ulam-oq-02-oq-02`: discharge the
remaining `sorry`s / infrastructure gaps, starting with the most self-contained
fixed-point-subspace and dimension-counting lemmas before attempting the full
equivariant-degree argument.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| borsuk-ulam-oq-02-oq-02 | Direct parent WIP proof being completed | equivariant maps, fixed-point subspaces |
| borsuk-ulam | Classical Z/2 base case | antipodal maps, degree |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Reduce to the maximal-torus / Z/p case and lift.
   - Why it might work: Compact Lie group actions restrict to tori where degree
     arguments are cleaner.
   - Risk: The lifting step needs substantial representation-theory infrastructure.

2. **Approach B**: Build equivariant degree directly for representation spheres.
   - Why it might work: Gives the general statement in one framework.
   - Risk: Equivariant degree is heavy to formalize from scratch in Mathlib.

### Key Difficulties

- Mathlib has limited equivariant-topology infrastructure.
- Fixed-point-subspace dimension bookkeeping across representations.

### What Would a Proof Need?

- Key lemma 1: Properties of the fixed-point subspace `V^G` and its complement.
- Key lemma 2: An equivariant-degree or cohomological obstruction giving a zero.
- Technical requirements: Representation-sphere and compact-Lie-group action API.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full theorem needs ~2000 lines of new infrastructure.
- Incremental progress on the self-contained lemmas is realistic per session.
- Mathlib's `RepresentationTheory` and topology libraries provide partial support.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: weeks (piecewise)
- If hard: unknown (full theorem)

## References

### Papers
- tom Dieck, "Transformation Groups", 1987 — equivariant Borsuk-Ulam and degree.

### Online Resources
- nLab: equivariant Borsuk-Ulam theorem — statement variants and hypotheses.

### Mathlib
- `Mathlib.RepresentationTheory.*` — group representations infrastructure.
- `Mathlib.Topology.*` — sphere / continuity API.

## Metadata

```yaml
tags:
  - topology
  - equivariant-topology
  - borsuk-ulam
  - representation-theory
  - lie-groups
related_proofs:
  - borsuk-ulam-oq-02-oq-02
  - borsuk-ulam
difficulty: high
source: gallery-gap
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 6/10
