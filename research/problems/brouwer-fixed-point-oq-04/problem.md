# Problem: Kakutani Fixed Point Theorem — Proof from Brouwer via Simplicial Approximation

**Slug**: brouwer-fixed-point-oq-04
**Created**: 2026-04-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

**Kakutani Fixed Point Theorem (1941)**: Let $S \subseteq \mathbb{R}^n$ be nonempty, compact, and convex. Let $F: S \to 2^S$ be an upper hemicontinuous correspondence with nonempty, closed, convex values. Then $F$ has a fixed point: $\exists x^* \in S,\ x^* \in F(x^*)$.

Currently in the gallery proof, the main Kakutani FPT is an axiom:
```lean
axiom kakutani_fixed_point {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) (hS_nonempty : S.Nonempty)
    (F : Correspondence S) (hF_uhc : IsUpperHemicontinuous F)
    (hF_nonempty : ∀ x, (F x).Nonempty) (hF_closed : ∀ x, IsClosed (F x : Set S))
    (hF_convex : ∀ x, Convex ℝ (F x : Set S)) :
    ∃ x : S, x ∈ F x
```

**Research Goal**: Prove this axiom as a theorem, reducing Kakutani to Brouwer's fixed point theorem.

### Plain Language

The gallery proof of Kakutani's theorem uses an axiom for the main result. The classical proof reduces Kakutani to Brouwer: approximate the set-valued map $F$ by a sequence of continuous single-valued maps, apply Brouwer to each, then take a cluster point of the fixed points. The goal is to formalize this reduction in Lean 4.

### Why This Matters

- Kakutani is used to prove Nash equilibrium existence in game theory
- Eliminating the axiom would improve the gallery proof from `axiomatized` to `verified`
- The simplicial approximation technique is broadly applicable across topology

## Known Results

### What's Already Proven

- Brouwer FPT is in Mathlib (`Mathlib.Topology.MetricSpace.Basic`)
- 1D Kakutani proved via IVT (in gallery, no axioms)
- `Correspondence`, `IsUpperHemicontinuous` defined in gallery's Lean file
- Singleton correspondences reduce to Brouwer (proved in gallery)

### What's Still Open

- Full proof of `kakutani_fixed_point` from Brouwer via simplicial approximation
- Or via Michael's selection theorem if available in Mathlib
- Nash equilibrium formalization (separate OQ)

### Our Goal

Determine the most tractable path from Brouwer to Kakutani in Lean 4, and formalize as much as possible. At minimum: document which Mathlib pieces exist and what remains to be built.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `brouwer-fixed-point` | Main Brouwer FPT | Topology, convexity |
| `brouwer-fixed-point-oq-04` | Parent: Kakutani axiomatized | Correspondences, UHC |
| `brouwer-fixed-point-oq-04-oq-03` | Nash equilibrium existence | Kakutani application |
| `brouwer-fixed-point-oq-01` | Sperner lemma path | Combinatorial topology |

## Initial Thoughts

### Potential Approaches

1. **Simplicial approximation**: Triangulate $S$ finely, define single-valued approx $f_\epsilon$ of $F$ on each simplex, apply Brouwer, take limit.
   - Why it might work: Classical proof strategy
   - Risk: Triangulation machinery may not be in Mathlib

2. **Michael's selection theorem**: Continuous selection from convex-valued UHC map, then apply Brouwer directly.
   - Why it might work: Michael's theorem may be in `Mathlib.Topology.MetricSpace.Selections`
   - Risk: Need to verify the theorem and its hypotheses match

3. **Schauder FPT as intermediate**: Prove finite-dim Schauder, then derive Kakutani.
   - Why it might work: Schauder is closely related and may have better Mathlib support
   - Risk: May just push the axiom one level up

### Key Difficulties

- Simplicial triangulation of convex compact sets in Lean
- Convergence of approximate fixed points requires sequential compactness
- UHC correspondences need careful treatment near the boundary

### What Would a Proof Need?

- Brouwer FPT: check `Mathlib.Topology.MetricSpace.BrouwerFixedPoint` or similar
- Triangulation: check `Mathlib.AlgebraicTopology.SimplicialSet`
- Sequential compactness: `IsCompact.isSeqCompact`
- Michael's selection: search `Mathlib` for `ContinuousSelection`

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Classical proof well-understood but simplicial approximation in Lean is non-trivial
- If Michael's selection theorem is available, difficulty drops to Medium
- Detailed proof sketch in gallery provides structure

**Estimated Effort**:
- Exploration (OBSERVE): 1-2 days to survey Mathlib
- If Michael's selection works: 1-2 weeks
- If full simplicial approx needed: 3-6 weeks

## References

### Papers
- Kakutani (1941). *A generalization of Brouwer's fixed point theorem*. Duke Math. J. 8(3):457-459.
- Fan (1952). *Fixed-point and minimax theorems in locally convex topological linear spaces*. PNAS.

### Mathlib
- `Mathlib.Analysis.Convex.Basic` — convexity
- `Mathlib.Topology.MetricSpace.Basic` — compactness
- Check: `Mathlib.Topology.MetricSpace.Selections` for Michael's selection
- Check: `Mathlib.AlgebraicTopology.SimplicialSet` for simplicial structure

## Metadata

```yaml
tags:
  - topology
  - fixed-point-theory
  - kakutani
  - brouwer
  - game-theory
  - correspondences
related_proofs:
  - brouwer-fixed-point
  - brouwer-fixed-point-oq-04
  - brouwer-fixed-point-oq-04-oq-03
difficulty: high
source: gallery-gap
created: 2026-04-04
```

**Significance**: 8/10
**Tractability**: 6/10
