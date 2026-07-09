# Problem: Projective Pappus–Brianchon incidence from ratio reciprocity

**Slug**: cevas-theorem-non-euclidean-oq-03-oq-01
**Created**: 2026-07-09T16:03:14-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $H = (A, B, C, D, E, F)$ be a hexagon whose vertices alternate on two
distinct lines (geodesics) $\ell_1 \ni A, C, E$ and $\ell_2 \ni B, D, F$ in a
projective plane over an ordered field — the Pappus configuration (a degenerate
conic $\ell_1 \cup \ell_2$). Write the three "diagonal" intersection points

$$
X = AB \cap DE, \qquad Y = BC \cap EF, \qquad Z = CD \cap FA .
$$

The **projective Pappus incidence theorem** asserts that $X, Y, Z$ are
collinear. Its projective dual is **Brianchon's theorem** for the dual
degenerate conic. The goal is to *derive* these incidence statements from the
already-formalized ratio-reciprocity engine, namely

$$
P(\mathrm{cfg}) \cdot P'(\mathrm{cfg}) \;=\;
\frac{bd}{dc}\frac{ce}{ea}\frac{af}{fb}\cdot
\frac{dc}{ce}\frac{ea}{af}\frac{fb}{bd} \;=\; 1
\qquad(\texttt{ceva\_dual\_reciprocal}),
$$

together with the multiplicative chaining laws
$P(c_1 \ast c_2) = P(c_1)\,P(c_2)$ and $P'(c_1 \ast c_2) = P'(c_1)\,P'(c_2)$.
Concretely: exhibit a Menelaus/transversal reading of the six hexagon sides such
that collinearity of $X, Y, Z$ becomes a product-equals-$1$ condition assembled
from the reciprocity identity by composition.

### Plain Language

The source gallery entry proved the *algebraic heart* of the non-Euclidean
Pappus–Brianchon theorems: the six side-measures of the hexagon satisfy a
telescoping identity $P \cdot P' = 1$, and this identity chains multiplicatively
when configurations are composed. But it deliberately stopped short of the
*geometric* statement everyone actually names "Pappus" — that the three
diagonal points of the hexagon lie on a common line. This problem asks to close
that gap: build the combinatorics of lines and intersection points on top of the
ratio reciprocity and recover the full projective incidence theorem (and, dually,
Brianchon), uniformly across Euclidean, spherical, and hyperbolic geometry.

### Why This Matters

Pappus's theorem is a cornerstone of projective geometry: it is equivalent to the
commutativity of the underlying coordinate field (Hessenberg's theorem links it
to Desargues), and it is the degenerate-conic special case of Pascal's mystic
hexagram. Showing that its incidence content is *exactly* the ratio reciprocity
already verified — plus a bookkeeping of which segments form the transversals —
would make the classical "multiply three Menelaus relations" proof fully formal
and, because the reciprocity holds verbatim for $\sin$ and $\sinh$ measures, would
deliver spherical and hyperbolic Pappus–Brianchon theorems from one algebraic
engine. This is a rare case where a purely algebraic Lean lemma is *one honest
step* from a famous geometric theorem.

## Known Results

### What's Already Proven

- **Ratio reciprocity `ceva_dual_reciprocal`**: $P(\mathrm{cfg}) \cdot P'(\mathrm{cfg}) = 1$ for every `GeneralizedCevianConfig` — gallery entry `cevas-theorem-non-euclidean-oq-03`.
- **Abstract Ceva–Brianchon duality `ceva_iff_dual`**: $P = 1 \iff P' = 1$ — same entry.
- **Multiplicativity / chaining `cevaProduct_comp`, `dualProduct_comp`, `ceva_comp_of_ceva`**: both alternating products are multiplicative under componentwise composition, and the Ceva condition is closed under it — same entry.
- **Spherical & hyperbolic instances**: `spherical_ceva_dual_reciprocal`, `hyperbolic_ceva_dual_reciprocal` — the closure relation with $\sin$ / $\sinh$ measures.
- **Non-Euclidean Menelaus `cevas-theorem-non-euclidean-oq-02`**: the transversal companion of Ceva, the relation the Pappus proof multiplies together.
- **Classical Pappus**: a standard theorem of projective geometry (Hessenberg, Coxeter); not yet in the Lean gallery in incidence form.

### What's Still Open

- No Lean formalization of the *incidence* statement "the three diagonal points are collinear" for the Pappus hexagon, in any of the three geometries.
- The precise dictionary translating "$X, Y, Z$ collinear" into a product-of-ratios $=1$ built from the six side-measures of a `GeneralizedCevianConfig`.
- The projective dual (Brianchon) incidence statement and a formal proof that point–line duality interchanges the two, with `ceva_iff_dual` as its ratio-algebra shadow.
- Extension from the degenerate conic (two geodesics) to a genuine non-degenerate conic (full Pascal/Brianchon).

### Our Goal

Formalize the *degenerate-conic (Pappus) incidence theorem* — collinearity of the
three diagonal points $X, Y, Z$ — over an ordered field, and prove it by reducing
collinearity (via a Menelaus criterion) to a product of side-ratios that the
existing `ceva_dual_reciprocal` and composition laws force to equal $1$. Deliver
the spherical and hyperbolic instances by reusing the parent's $\sin$/$\sinh$
measure builders. Full Brianchon and the non-degenerate conic are stretch goals.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cevas-theorem-non-euclidean-oq-03 | Source: proves the ratio reciprocity $P\cdot P'=1$ and the composition/chaining laws this problem must lift to incidence | telescoping products, `field_simp`, `ring`, `positivity` |
| cevas-theorem-non-euclidean-oq-02 | Non-Euclidean Menelaus — the transversal relation the classical Pappus proof multiplies three times | ratio algebra over constant-curvature measures |
| cevas-theorem-non-euclidean | Parent: defines `GeneralizedCevianConfig`, `generalizedCevaProduct`, and the $\sin$/$\sinh$ measure builders | unified constant-curvature ratio framework |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Menelaus-chaining (classical, algebraic)**: Realize the Pappus
   diagonal triangle as three transversals, apply the non-Euclidean Menelaus
   relation to each, and multiply. The product collapses via `ceva_dual_reciprocal`
   and `cevaProduct_comp` to the single collinearity condition.
   - Why it might work: this is literally the classical proof, and the multiplicative
     step is *already verified* (`ceva_comp_of_ceva`); only the geometric-to-ratio
     dictionary is missing.
   - Risk: setting up an honest incidence layer (points, lines, `Collinear`) over an
     ordered field, and proving a Menelaus *criterion* (ratio $=1 \Rightarrow$
     collinear), is substantial new formalization not present in the algebraic parent.

2. **Approach B — Coordinate / projective-plane model**: Work in $\mathbb{P}^2(K)$
   for an ordered field $K$ (or Mathlib's `Projectivization`), place the six vertices,
   compute the three intersection points, and prove collinearity by a determinant
   identity, *then* show that determinant equals the reciprocity product.
   - Why it might work: determinants make collinearity decidable and connect cleanly
     to signed ratios; avoids inventing a Menelaus criterion from scratch.
   - Risk: heavy coordinate algebra; the link to the abstract `GeneralizedCevianConfig`
     may become a re-derivation rather than a reuse, weakening the "one engine" story.

### Key Difficulties

- There is currently **no incidence infrastructure** in the parent lineage — only
  the field algebra of positive measures. Collinearity, "line through two points",
  and intersection points must be built or imported.
- The reciprocity is stated with *unsigned* positive measures; genuine projective
  incidence needs *signed* ratios (Menelaus's $-1$), so a sign/orientation
  reconciliation is required to bridge the two.
- Transferring to spherical/hyperbolic geometry requires that the incidence layer
  itself (not just the ratios) be geometry-uniform, which the parent does not provide.

### What Would a Proof Need?

- **Menelaus criterion (converse)**: three points on the sides of a triangle are
  collinear iff a signed product of ratios equals $-1$ — as a reusable lemma over an
  ordered field.
- **Dictionary lemma**: an identification of the six Pappus side-measures with the
  entries of `GeneralizedCevianConfig` such that the collinearity product *is* (up to
  sign) $P$ or $P'$.
- **Assembly lemma**: multiply the three transversal relations using `cevaProduct_comp`
  / `dualProduct_comp` and collapse with `ceva_dual_reciprocal`.
- **Technical requirements**: an ordered-field or projective-plane incidence model
  (possibly Mathlib's `Projectivization` / affine `Collinear`), signed-ratio arithmetic,
  and re-use of the parent's $\sin$/$\sinh$ builders for the non-Euclidean instances.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The *algebraic core* is already done and axiom-free; the classical proof strategy
  is known, so this is not a search for a proof but a formalization of a known route.
- However, it demands new incidence infrastructure (collinearity, intersection points,
  a Menelaus criterion) and a signed/unsigned ratio reconciliation absent from the
  parent — the hardest part is the geometric layer, not the algebra.
- Mathlib provides `Projectivization`, affine `Collinear`, and `Matrix.det` tools that
  make a coordinate proof feasible, but wiring them to the abstract config is nontrivial.

**Estimated Effort**:
- Exploration: 3–5 days (choose incidence model; prove/find a Menelaus criterion)
- If tractable: 2–4 weeks (Euclidean incidence Pappus reusing the reciprocity)
- If hard: unknown (full Brianchon duality + non-degenerate conic; signed spherical/hyperbolic incidence)

## References

### Papers
- Pappus of Alexandria, *Collection (Synagoge), Book VII* (c. 340) — original hexagon theorem.
- C. J. Brianchon, *Sur les surfaces courbes du second degré* (1810) — projective dual for circumscribed hexagons.
- G. Hessenberg, *Beweis des Desarguesschen Satzes aus dem Pascalschen* (1905) — Pappus ⇒ Desargues, field-commutativity link.
- A. Papadopoulos, *Hyperbolic analogues of classical theorems in spherical geometry* (2014) — transferring incidence/ratio theorems across constant-curvature geometries.

### Online Resources
- https://en.wikipedia.org/wiki/Pappus%27s_hexagon_theorem — statement, diagram, and standard Menelaus-chaining proof.
- https://en.wikipedia.org/wiki/Brianchon%27s_theorem — projective dual and duality principle.

### Mathlib
- `Mathlib.LinearAlgebra.Projectivization.Basic` — projective spaces over a field, points/lines.
- `Mathlib.LinearAlgebra.AffineSpace.Independent` / `Collinear` — collinearity predicates.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` — determinant criterion for collinearity.
- `Mathlib.Tactic` (`field_simp`, `ring`, `positivity`) — the ratio-algebra tactics already used in the parent.

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
  - cevas-theorem-non-euclidean-oq-02
  - cevas-theorem-non-euclidean
difficulty: high
source: proof-suggestion
created: 2026-07-09T16:03:14-07:00
```
