# Problem: Constructive 2D Borsuk-Ulam via Tucker Lemma

**Slug**: borsuk-ulam-oq-03-oq-03
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall f : S^2 \to \mathbb{R}^2 \text{ continuous}, \exists x \in S^2, f(x) = f(-x)
$$

Prove constructively using Tucker's lemma and combinatorial approximation (no homology or degree theory).

### Plain Language

For any continuous map from the sphere to the plane, there must be a pair of antipodal points (opposite points on the sphere) that map to the same value. We want a purely combinatorial proof using Tucker's lemma instead of algebraic topology.

### Why This Matters

The Borsuk-Ulam theorem is fundamental in topology with applications in combinatorics (ham sandwich theorem, necklace splitting). A constructive proof gives algorithmic content: how to actually find the antipodal pair.

## Known Results

### What's Already Proven

- 1D Borsuk-Ulam via IVT — `borsuk-ulam-oq-03` (constructive, in gallery)
- Mathlib has `Topology.BorsukUlam` — uses cohomological methods (non-constructive)
- Tucker's lemma ⟹ Borsuk-Ulam (classical math, see Matoušek "Using the Borsuk-Ulam Theorem")

### What's Still Open

- Fully constructive 2D proof in Lean 4
- Formalization of Tucker's lemma for n=2
- The approximation bridge (Tucker → BU)

### Our Goal

Formalize a constructive proof of the 2D Borsuk-Ulam theorem using Tucker's lemma and simplicial approximation.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| borsuk-ulam-oq-03 | 1D constructive BU via IVT | Intermediate value theorem, antipodal maps |
| borsuk-ulam-oq-02 | Equivariant BU generalizations | Group actions on spheres |

## Initial Thoughts

### Potential Approaches

1. **Tucker's lemma via Sperner**: Reduce Tucker to Sperner's lemma (which may be partially formalized)
   - Why it might work: Sperner's lemma has been formalized in similar systems
   - Risk: The reduction involves barycentric subdivision details

2. **Direct combinatorial Tucker**: Formalize Tucker's lemma from first principles for n=2
   - Why it might work: Self-contained, no dependencies on Sperner
   - Risk: More work, needs careful triangulation handling

### Key Difficulties

- Mathlib's simplicial complex infrastructure may be limited
- Approximation argument requires careful epsilon-delta work
- Connecting discrete Tucker output to continuous BU conclusion

### What Would a Proof Need?

- Key lemma 1: Tucker's lemma for antipodally symmetric labelings of triangulated B²
- Key lemma 2: Approximation — continuous f can be approximated by simplicial maps
- Technical requirements: Triangulation of B², simplicial maps, convergence

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Tucker's lemma is well-understood combinatorially
- The 1D proof in gallery provides a template for the constructive style
- Main challenge is Lean formalization of triangulations

## References

### Papers
- Matoušek, "Using the Borsuk-Ulam Theorem" — comprehensive treatment
- Tucker, "Some topological properties of disk and sphere" (1946) — original

### Mathlib
- `Topology.BorsukUlam` — non-constructive proof (for comparison)
- `Topology.ContinuousOn` — continuity infrastructure

## Metadata

```yaml
tags:
  - topology
  - constructive-math
  - borsuk-ulam
  - tucker-lemma
  - combinatorial-topology
related_proofs:
  - borsuk-ulam-oq-03
  - borsuk-ulam-oq-02
difficulty: medium-high
source: gallery-gap
created: 2026-03-06
```

**Significance**: 7/10
**Tractability**: 6/10
