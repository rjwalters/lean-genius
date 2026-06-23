# Problem: Exotic G-Representations with Strictly Higher Equivariant Borsuk-Ulam Dimension

**Slug**: borsuk-ulam-oq-02-oq-01-oq-01-oq-02
**Created**: 2026-04-12
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Given the equivariant Borsuk-Ulam dimension `buDim(G, V, W)` measuring the minimum dimension of an equivariant map `S(V) → S(W)` that avoids antipodal coincidence, determine whether there exist G-representations for composite groups G (e.g., G = Z/pq) where the Borsuk-Ulam dimension is strictly higher than for any cyclic group of prime order.

### Plain Language

The classical Borsuk-Ulam theorem says that any continuous map from Sⁿ to Rⁿ must send some pair of antipodal points to the same value. This generalizes to equivariant maps under group actions: for a group G acting on spheres S(V) and S(W), there is a minimum "Borsuk-Ulam dimension" below which no equivariant map can avoid coincidences.

The question is: do composite groups (like Z/6 = Z/2 × Z/3) exhibit strictly richer Borsuk-Ulam phenomena than prime-order cyclic groups? Specifically, are there representations where the composite structure forces the BU dimension higher than any prime-order case?

### Why This Matters

- Equivariant topology is foundational for applications in topological combinatorics (Lovász-Kneser, ham sandwich theorems)
- Understanding how group structure affects BU dimension connects representation theory to geometric topology
- A positive answer would show composite groups have genuinely new topological phenomena, not just products of prime-order effects

## Known Results

### What's Already Proven

- Classical Borsuk-Ulam for Z/2 actions (gallery proof: `borsuk-ulam`)
- BU dimension bounds for cyclic groups Z/p (prime order)
- Upper bound `buDim(n,d) ≤ buDimFormula(n,d)` (related OQ in gallery)

### What's Still Open

- Whether composite groups give strictly higher BU dimensions
- Explicit examples of "exotic" representations for composite groups
- Tight bounds on buDim for non-prime cyclic groups

### Our Goal

Formalize in Lean 4: either construct an explicit G-representation for a composite group G showing strictly higher buDim than any prime-order cyclic group, or prove an impossibility result showing buDim for composite groups reduces to the prime factors.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| borsuk-ulam | Parent proof — classical BU theorem | Equivariant topology, degree theory |

## Initial Thoughts

### Potential Approaches

1. **Explicit construction for Z/6**: Find representations V, W of Z/6 where buDim(Z/6, V, W) > max(buDim(Z/2, V', W'), buDim(Z/3, V'', W''))
   - Why it might work: The interaction between 2- and 3-torsion could create new obstructions
   - Risk: May require heavy representation theory not in Mathlib

2. **Reduction to prime factors**: Show buDim for Z/pq decomposes via restriction to Sylow subgroups
   - Why it might work: Smith theory and localization techniques are well-understood
   - Risk: Could show impossibility (no exotic phenomena), but that's still a valuable result

### Key Difficulties

- Equivariant topology infrastructure in Mathlib may be limited
- Representation theory for composite cyclic groups needs careful setup
- Computing buDim concretely requires either explicit obstruction theory or clever construction

### What Would a Proof Need?

- Group action infrastructure: representations of Z/n on spheres
- buDim definition formalized (from parent gallery proof context)
- Either: explicit construction + lower bound proof, or: decomposition theorem

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- The question is an open conjecture (tagged as such in the pool)
- Even partial results (e.g., for specific small groups) are publishable
- Mathlib has group action basics but limited equivariant topology

**Estimated Effort**:
- Exploration: 1-2 days (survey what's in Mathlib for group reps + BU)
- If tractable: 1-2 weeks for a specific example
- If hard: Pivot to formalizing known bounds for prime-order case

## References

### Mathlib
- `Mathlib.Topology.Algebra.Group.Basic` — group action topology
- `Mathlib.RepresentationTheory` — representation theory foundations
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` — cyclic group structure

## Metadata

```yaml
tags:
  - topology
  - borsuk-ulam
  - equivariant
  - group-actions
  - representation-theory
  - open-conjecture
related_proofs:
  - borsuk-ulam
difficulty: medium-high
source: gallery-gap
created: 2026-04-12
```
