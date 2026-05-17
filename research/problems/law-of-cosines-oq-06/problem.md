# Problem: Formalize Law of Sines via `InnerProductGeometry.angle`

**Slug**: law-of-cosines-oq-06
**Created**: 2026-04-05T23:12:43-07:00
**Status**: Completed
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For any triangle in the Euclidean plane with vertices $A, B, C \in \mathbb{R}^2$, side
lengths $a = \|B - C\|$, $b = \|A - C\|$, $c = \|A - B\|$, and interior angles
$\alpha, \beta, \gamma$ opposite those sides,

$$
\frac{a}{\sin \alpha} \;=\; \frac{b}{\sin \beta} \;=\; \frac{c}{\sin \gamma}.
$$

Concretely in Lean (`proofs/Proofs/LawOfSinesOQ06.lean`) the formalization is built
on top of `EuclideanSpace ℝ (Fin 2)` and `InnerProductGeometry.angle`, with the
2D cross product `cross2D` supplying the signed area.

### Plain Language

The ratios of side length to the sine of the opposite angle are the same for all
three sides of a planar triangle. Mathlib already has the Law of Cosines and the
machinery for inner-product angles, but lacked an axiom-free formalization of the
sister identity. This entry closes that gap by deriving the Law of Sines from
the 2D Lagrange identity and `Real.sin_arccos`, with the area-of-triangle calculation
serving as the bridge between the algebraic and geometric formulations.

### Why This Matters

The Law of Sines is one of the foundational results of Euclidean triangle
geometry. Establishing it on Mathlib's `InnerProductGeometry.angle` API — without
introducing any new axioms — extends the suite of triangle-geometry results that
can be reused downstream (e.g. circumradius identities, spherical analogues such
as `SphericalLawOfSines.lean`).

## Known Results

### What's Already Proven

- `LawOfCosines.lean` — direct parent, uses `inner_mul_le_norm_mul_norm`,
  `cos_angle_of_inner`.
- `pythagorean-theorem` — the right-angle degenerate case ($\gamma = \pi/2$).
- Mathlib: `InnerProductGeometry.angle`, `Real.sin_arccos`, `Real.sqrt_mul`,
  `Real.sqrt_sq`, `Real.sqrt_sq_eq_abs`.

### What's Still Open

Nothing in scope — this entry was selected as a formalization task with a clear
path, not as an open problem. Spherical and hyperbolic analogues live in
`SphericalLawOfSines.lean` and its descendants.

### Our Goal

Formalize $a/\sin\alpha = b/\sin\beta = c/\sin\gamma$ in Mathlib with **0 axioms,
0 sorries**, building only on `InnerProductGeometry.angle` and the 2D cross
product.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `law-of-cosines` | Direct parent | `inner_mul_le_norm_mul_norm`, `cos_angle_of_inner` |
| `pythagorean-theorem` | Degenerate case at $\gamma = \pi/2$ | Inner-product norms |
| `spherical-law-of-sines` | Spherical analogue | Same angle API, unit-sphere geometry |

## Initial Thoughts

### Potential Approaches

1. **Area-equality approach (taken)**: compute the triangle area three ways via
   $\tfrac{1}{2} \cdot ab \cdot \sin C$, equate, and rearrange.
2. **Circumradius approach**: invoke $R = abc / (4 \cdot \mathrm{Area})$ to obtain
   $a / \sin\alpha = 2R$. More machinery; deferred.
3. **Inscribed-angle theorem**: classical synthetic route. Requires more
   geometry infrastructure than Mathlib currently has at this level.

### Key Difficulties

- Bridging `Real.sin (InnerProductGeometry.angle u v)` (defined as
  `sin (arccos (⟨u,v⟩ / (‖u‖‖v‖)))`) to a polynomially-tractable form.
- Discharging non-negativity of `1 - (⟨u,v⟩ / (‖u‖‖v‖))^2` to use
  `Real.sqrt_mul`.

### What a Proof Needed

- **Sin–cross identity**: $\sin(\angle u v) \cdot \|u\| \cdot \|v\| = |u \times v|$
  (in 2D), proved as `sin_angle_mul_norms`.
- **2D Lagrange identity**: $\|u\|^2 \|v\|^2 = \langle u,v\rangle^2 + (u \times v)^2$,
  proved by `ring`.
- **Cauchy–Schwarz** in $\mathbb{R}^2$: from Lagrange + `sq_nonneg (cross2D u v)`.

## Tractability Assessment

**Difficulty**: Medium — clear Mathlib path, one non-obvious algebraic identity.

**Justification**: Tractability 8/10 at selection. Mathlib provides
`InnerProductGeometry.angle` and `Real.sin_arccos` unconditionally; the bulk of
the work was discovering the calc chain
$\sqrt{1-c^2} \cdot N = \sqrt{(1-c^2) N^2} = \sqrt{\mathrm{cross}^2} = |\mathrm{cross}|$.

## Outcome

**Completed 2026-04-13** — Session 1 (single FRESH session).

Result: `LawOfSinesOQ06.lean` (309 lines, 0 axioms, 0 sorries). The original
`axiom sin_angle_mul_norms` was eliminated; the full Law of Sines now follows
mechanically from `sin_angle_mul_norms` (lemma) plus the area-equality argument.
See `knowledge.md` for the full proof of `sin_angle_mul_norms`.
