# Problem: Sperner's Lemma as Alternative Combinatorial Proof of Brouwer

**Slug**: brouwer-fixed-point-oq-03
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Given a continuous map $f : B^n \to B^n$ on the closed unit ball, there exists $x \in B^n$
with $f(x) = x$. The Sperner route proves this via:

1. **Sperner's Lemma**: Any Sperner-labeled triangulation of $\Delta^n$ contains an
   odd number of fully-labeled simplices (in particular, at least one).
2. **Convergence**: Vertices of fully-labeled simplices in successively finer
   triangulations have a convergent subsequence (compactness of $B^n$).
3. **Fixed point**: The limit is a fixed point by continuity of $f$.

### Plain Language

Prove Brouwer's Fixed Point Theorem using Sperner's Lemma — a combinatorial result
about colored triangulations that avoids all homology theory. Unlike the existing
gallery proof (which uses the No-Retraction Theorem via homology), this is a fully
elementary combinatorial proof accessible at undergraduate level.

### Why This Matters

The existing `brouwer-fixed-point` proof is axiomatized (requires homology axioms).
A Sperner-based proof would:
- Be entirely combinatorial (no topology prerequisites beyond compactness)
- Be constructive: gives an algorithm to approximate fixed points
- Potentially be fully axiom-free (0 sorries)
- Complement the 1D proof via IVT already in gallery

## Known Results

### What's Already Proven (Gallery)

- `brouwer-fixed-point` — Main theorem via No-Retraction (homology-based, axiomatized)
- `brouwer-fixed-point-oq-01` — 1D elementary proof via IVT (verified)
- `brouwer-fixed-point-oq-02` — Computational complexity of approximate fixed points
- `brouwer-fixed-point-oq-04` — Kakutani Fixed Point Theorem

### Mathlib Availability

- Compactness of closed balls: likely available
- Sequential compactness (Bolzano-Weierstrass): available
- Simplicial complex / triangulation: may be partial
- Sperner's Lemma: check `Mathlib.Combinatorics` — may not exist yet

### What's Still Open

- Sperner's Lemma in Lean (n-dim) — target of Mathlib initiative per project memory
- The convergence argument for the fixed point
- Full Sperner → Brouwer chain

### Our Goal

Formalize the complete Sperner → Brouwer proof chain in Lean 4, ideally with 0 sorries,
providing a combinatorial alternative to the homology-based proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `brouwer-fixed-point` | Theorem we're re-proving by a new route | Homology, No-Retraction |
| `brouwer-fixed-point-oq-01` | 1D Brouwer via IVT (elementary precedent) | IVT, analysis |
| `brouwer-fixed-point-oq-04` | Kakutani (uses Brouwer internally) | Set-valued maps |

## Initial Thoughts

### Potential Approaches

1. **Full n-dim Sperner Route**:
   - Define simplicial triangulation of $\Delta^n$ or $B^n$
   - Define Sperner labeling (boundary condition)
   - Prove Sperner's Lemma by dimension induction
   - Prove fixed point via sequential compactness
   - Risk: triangulation formalization may be too complex without Mathlib support

2. **2D Case First** (Triangle → Ball in 2D):
   - Prove Sperner for triangles (2D simplices)
   - Prove Brouwer for the disk via 2D Sperner
   - Risk: still requires triangulation formalization

3. **KKM Lemma Route** (equivalent to Sperner):
   - Knaster-Kuratowski-Mazurkiewicz lemma is often easier to formalize
   - Equivalent to Brouwer, and the proof is more topological
   - Risk: may not be more accessible than homology route

### Key Difficulties

- Formalizing simplicial triangulations in Lean 4
- The Sperner labeling condition on the boundary
- Sequential compactness (compactness of $B^n$ in Lean)
- The mesh → 0 argument requires careful epsilon management

### What Would a Proof Need?

- Sperner's Lemma (exists in Mathlib? — check)
- `IsCompact (closedBall 0 1)` (likely in Mathlib.Topology.MetricSpace)
- Sequential compactness / Bolzano-Weierstrass for $\mathbb{R}^n$
- `ContinuousMap.fixed_point` or similar

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Sperner's Lemma itself is combinatorially accessible
- Triangulation formalization is the main technical bottleneck
- Mathlib may not have simplicial complex infrastructure ready
- The Lean Genius Mathlib Sperner initiative (in memory) suggests active work nearby
- The 2D special case might be tractable as a concrete contribution

**Estimated Effort**:
- Exploration: 1-2 days (survey Mathlib simplicial complex support)
- If Mathlib has Sperner: 3-5 days for the full proof
- If Mathlib missing Sperner: weeks (must build from scratch)

## References

### Papers
- Sperner, E., "Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes"
  (1928) — original Sperner's Lemma paper
- Knaster, B., Kuratowski, C., Mazurkiewicz, S., "Ein Beweis des Fixpunktsatzes für
  n-dimensionale Simplexe" (1929) — KKM lemma (equivalent route)

### Mathlib
- `Mathlib.Topology.MetricSpace.Basic` — compactness of closed balls
- `Mathlib.AlgebraicTopology.SimplexCategory` — simplicial infrastructure
- Check `Mathlib.Combinatorics` for any Sperner-related results

## Metadata

```yaml
tags:
  - topology
  - fixed-point-theory
  - algebraic-topology
  - sperner
  - combinatorial-proof
  - wiedijk-100
related_proofs:
  - brouwer-fixed-point
  - brouwer-fixed-point-oq-01
  - brouwer-fixed-point-oq-04
difficulty: medium-high
source: gallery-gap
created: 2026-04-05
```
