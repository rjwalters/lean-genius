# Problem: Prove the flat-limit convergence formally: sin_κ(x) → x as κ → 0, so the curv...

**Slug**: cevas-theorem-non-euclidean-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sin_\kappa(x) := \frac{\sin(\sqrt{\kappa}\,x)}{\sqrt{\kappa}} \;\xrightarrow[\kappa\to 0]{}\; x, \qquad\text{so the curvature-}\kappa\text{ Ceva condition} \to \text{the Euclidean one}
$$

### Plain Language

Prove formally that the curvature-scaled sine sin_κ(x) converges to x as the curvature κ → 0, so that the curvature-κ Ceva ratio condition on a triangle degenerates continuously to the flat (Euclidean) Ceva condition for triangles on a manifold of shrinking curvature.

### Why This Matters

This is the formal bridge showing non-Euclidean (spherical/hyperbolic) Ceva theorem is a genuine generalization of the Euclidean one: the classical result is recovered in the zero-curvature limit. It pins down the limiting behaviour that makes the curved statement a deformation of the flat statement.

## Known Results

### What's Already Proven

- Parent `cevas-theorem-non-euclidean-oq-01` formalizes the curvature-κ Ceva condition using generalized sine functions.
- Mathlib: `Real.sin`, `Real.tendsto_sin_div`/`Real.sin_div_tendsto`-style limits, `Filter.Tendsto`, `Real.sqrt`.

### What's Still Open

This specific leaf — extracted as an open question from the parent proof `cevas-theorem-non-euclidean-oq-01` — has not yet been formalized in the gallery.

### Our Goal

Prove `Tendsto (fun κ => sin_κ x) (𝓝[≠] 0 or 𝓝 0⁺) (𝓝 x)` and conclude the Ceva ratio product tends to the Euclidean product.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cevas-theorem-non-euclidean-oq-01` | parent: curvature-κ Ceva condition | spherical/hyperbolic trig |
| `cevas-theorem` | Euclidean Ceva's theorem | ratios, barycentric |

## Initial Thoughts

### Potential Approaches

1. **Reuse parent machinery**: The parent `cevas-theorem-non-euclidean-oq-01` is verified (0-axiom); specialize / instantiate its main results to this leaf rather than re-deriving from scratch.
2. **Lean directly on Mathlib**: Several of the required notions already exist in Mathlib (see References); the work is connecting them to the parent's statement.

### What Would a Proof Need?

- Import and apply the parent proof's verified lemmas.
- Bridge lemmas connecting the parent's formulation to standard Mathlib definitions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Direct extension of a verified, 0-axiom parent proof.
- Required supporting definitions exist in Mathlib.
- Clear first step: instantiate / specialize the parent result.

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — `Real.sin` and limits.
- `Filter.Tendsto`, `Real.sin_eq_zero_iff`, small-angle estimates.

## Metadata

```yaml
tags:
  - geometry
  - non-euclidean-geometry
  - ceva
  - curvature
  - research
related_proofs:
  - cevas-theorem-non-euclidean-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
