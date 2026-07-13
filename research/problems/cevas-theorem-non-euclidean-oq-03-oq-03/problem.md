# Problem: Non-Degenerate Conic Brianchon from the Hexagon Ratio Algebra

**Slug**: cevas-theorem-non-euclidean-oq-03-oq-03
**Created**: 2026-07-09T16:43:20-07:00
**Status**: Active
**Source**: user-request

## Problem Statement

### Formal Statement

$$
\text{If a hexagon } A_1B_1C_1A_2B_2C_2 \text{ is circumscribed about a non-degenerate conic } \mathcal{C},
\text{ then its three principal diagonals are concurrent (Brianchon).}
$$

Concretely, the source entry proves the geometry-independent hexagon closure relation
$$
P(\mathrm{cfg}) \cdot P'(\mathrm{cfg}) = \frac{bd}{dc}\frac{ce}{ea}\frac{af}{fb} \cdot \frac{dc}{ce}\frac{ea}{af}\frac{fb}{bd} = 1
$$
only for the **degenerate** conic — the Pappus case, where the six vertices alternate on two geodesics. This problem asks to promote that same alternating-ratio invariant to a **genuine non-degenerate conic** $\mathcal{C}$, so that the six tangent-contact side-measures still satisfy a telescoping reciprocity and the resulting concurrence condition is exactly Brianchon's theorem for a hexagon circumscribed about $\mathcal{C}$.

### Plain Language

The source proof (`cevas-theorem-non-euclidean-oq-03`) captured the algebraic skeleton of the Pappus–Brianchon story: the six side-measures of a hexagon telescope into the reciprocity $P\cdot P' = 1$, and this multiplies cleanly under composition. But it only did so for the *degenerate* conic — two geodesics carrying the alternating vertices — which is the Pappus special case, not the full Brianchon theorem. This problem asks to lift that same ratio algebra to a **real, non-degenerate conic** (an ellipse-like curve inscribed in / circumscribed about the hexagon). The goal is to define, for a hexagon whose six sides are tangent to a conic, the analogue of the six measures, prove the closure relation still holds by a telescoping argument, and derive the Brianchon concurrence of the three principal diagonals — uniformly for length, sine, and hyperbolic-sine measures so that the spherical and hyperbolic Brianchon theorems come out together.

### Why This Matters

Brianchon's theorem (1810) is the projective dual of Pascal's hexagram and a cornerstone incidence result of conic geometry. The source entry deliberately restricted itself to the degenerate conic (Pappus), leaving the genuine-conic Brianchon statement as explicit future work. Closing this gap would show that the verified ratio-reciprocity engine is not an artifact of the two-line degeneration but the true algebraic core of conic-hexagon incidence, and — because the reciprocity holds verbatim for `sin` and `sinh` measures — it would simultaneously deliver the spherical and hyperbolic Brianchon theorems from one uniform argument.

## Known Results

### What's Already Proven

- `ceva_dual_reciprocal` — the hexagon closure relation $P\cdot P' = 1$ for the degenerate conic, formalized in `cevas-theorem-non-euclidean-oq-03` (`src/data/proofs/cevas-theorem-non-euclidean-oq-03/meta.json`).
- `ceva_iff_dual`, `cevaProduct_comp`, `dualProduct_comp`, `ceva_comp_of_ceva` — the abstract Ceva–Brianchon duality and the multiplicative chaining laws, plus spherical/hyperbolic instances, in the same source entry.
- Non-Euclidean Menelaus (`cevas-theorem-non-euclidean-oq-02`) — the transversal companion that supplies the collinearity/concurrence criteria.

### What's Still Open

- No formalization of the six tangent-contact side-measures for a hexagon circumscribed about a genuine non-degenerate conic.
- No proof that the closure reciprocity survives the passage from two geodesics (degenerate conic) to a genuine conic.
- No Lean statement of Brianchon concurrence of the three principal diagonals for the non-degenerate case, in any of the three constant-curvature geometries.

### Our Goal

Define a `NonDegenerateConicHexagon` configuration whose six positive measures are the tangent-segment measures of a hexagon circumscribed about a conic, prove the closure relation $P\cdot P' = 1$ for it (reusing the telescoping argument), and derive the Brianchon concurrence condition — then specialize verbatim to `sin` (sphere) and `sinh` (hyperbolic) via the parent's measure builders. Full projective incidence (points and lines) is a stretch goal; the primary target is the ratio-algebraic Brianchon invariant for the non-degenerate conic.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cevas-theorem-non-euclidean-oq-03 | Direct parent: proves the closure relation $P\cdot P'=1$ and composition laws for the degenerate (Pappus) conic; this problem lifts them to a genuine conic | Telescoping ratio algebra, `field_simp`, `positivity`, `ring` over positive reals |
| cevas-theorem-non-euclidean-oq-02 | Non-Euclidean Menelaus, the transversal companion supplying the concurrence/collinearity criteria used to phrase Brianchon | Unified measure framework across constant-curvature geometries |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Tangent-length measures via a conic model**: Model the non-degenerate conic in the projective/affine plane, take the six tangent lines of the circumscribed hexagon, and let the six measures be the tangent-segment lengths (or their `sin`/`sinh` analogues) between consecutive contact points. Show these satisfy the same alternating structure as the parent's `GeneralizedCevianConfig`, then invoke `ceva_dual_reciprocal` almost verbatim.
   - Why it might work: the parent's closure relation is purely about six positive reals with an alternating cancellation pattern; if the tangent measures reproduce that pattern, the identity transfers with no new algebra.
   - Risk: the tangent measures of a genuine conic need not exhibit the exact same telescoping pattern as the two-line degeneration; establishing that they do may require a real conic-geometry lemma (e.g. equal tangent segments / a power-of-a-point analogue) not yet in Mathlib.

2. **Approach B — Degeneration/limit from the two-line case**: Treat the non-degenerate conic as a deformation of the degenerate pair of geodesics and argue the ratio invariant is preserved under the deformation, transporting the already-proven closure relation to the limit conic.
   - Why it might work: it reuses the verified degenerate-case identity directly and only needs a continuity/invariance argument for the ratio product.
   - Risk: making "deformation of a conic" precise in Lean is heavy; the invariance of the ratio product under such a family is itself a nontrivial theorem and may be harder than a direct tangent-measure computation.

### Key Difficulties

- Formalizing tangent segments to a non-degenerate conic (and their spherical/hyperbolic analogues) is not currently supported by Mathlib and may require substantial groundwork.
- Establishing that the six conic-tangent measures obey the exact alternating cancellation pattern that makes the parent's telescoping proof go through — the geometric input distinguishing the genuine conic from the two-line degeneration.
- Phrasing "the three principal diagonals are concurrent" as a ratio-product condition and matching it to the reciprocity, uniformly across length, `sin`, and `sinh`.

### What Would a Proof Need?

- Key lemma 1: a `NonDegenerateConicHexagon` structure with six positive tangent-contact measures and a proof that they satisfy the alternating pattern of `GeneralizedCevianConfig`.
- Key lemma 2: the closure relation $P\cdot P' = 1$ for this structure (ideally by reduction to `ceva_dual_reciprocal`), plus a Brianchon concurrence condition phrased as $P = 1$ and its dual.
- Technical requirements: a conic-tangent / equal-tangent-segment lemma over an ordered field, and the `sin`/`sinh` measure builders reused from the parent for the spherical and hyperbolic instances.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The algebraic core (the telescoping reciprocity) is already verified in the parent, so if the tangent-contact measures reproduce the alternating pattern, the identity transfers cheaply.
- The genuine difficulty is geometric: formalizing conic tangents and their measures, which Mathlib does not directly provide, pushing the effort above a routine extension.
- Similar unified-measure transfers (Euclidean → spherical → hyperbolic) already worked in the OQ-03 lineage, giving a template for the non-Euclidean specializations once the abstract structure is in place.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 1–2 weeks
- If hard: unknown (blocked on missing conic-tangent infrastructure)

## References

### Papers
- Brianchon, C. J., "Sur les surfaces courbes du second degré", *Journal de l'École Polytechnique*, 1810 — the original Brianchon theorem, projective dual of Pascal for hexagons circumscribed about a conic.
- Papadopoulos, A., "Hyperbolic analogues of classical theorems in spherical geometry", 2014 — context for transferring classical incidence/ratio theorems across constant-curvature geometries.

### Online Resources
- https://en.wikipedia.org/wiki/Brianchon%27s_theorem — statement and projective duality with Pascal's theorem.
- https://en.wikipedia.org/wiki/Pappus%27s_hexagon_theorem — the degenerate-conic special case handled by the parent entry.

### Mathlib
- `Mathlib.Tactic` — `field_simp`, `positivity`, `ring` for the telescoping ratio identities over positive reals.
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — `Real.sin` / `Real.sinh` for the spherical and hyperbolic measure builders.
- `Mathlib.LinearAlgebra.Projectivization.Basic` — projective-plane infrastructure for the conic and its tangent lines (incidence stretch goal).

## Metadata

```yaml
tags:
  - geometry
  - non-euclidean
  - projective-geometry
  - pappus
  - brianchon
  - ceva
  - ratio-algebra
related_proofs:
  - cevas-theorem-non-euclidean-oq-03
difficulty: medium
source: user-request
created: 2026-07-09T16:43:20-07:00
```
