# Problem: The Sylvester–Gallai Theorem — Existence of an Ordinary Line

**Slug**: sylvester-gallai-theorem-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: seeker-selected <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
S \text{ finite},\ |S| \ge 3,\ \neg\,\mathrm{Collinear}(S)
\ \Longrightarrow\
\exists\, \ell,\ \bigl|\{p \in S : p \in \ell\}\bigr| = 2.
$$

Let $S \subseteq \mathbb{R}^2$ be a finite set of points that is **not** collinear
(they do not all lie on a single line). Then there exists a line that passes through
**exactly two** points of $S$ — an *ordinary line*.

### Plain Language

Take any finite collection of dots in the plane that do not all sit on one straight
line. The theorem promises you can always find a straight line that hits exactly two of
the dots — no more. This is surprising: it says you cannot arrange finitely many
non-collinear points so that *every* line through two of them is forced to pass through a
third.

### Why This Matters

The Sylvester–Gallai theorem (conjectured by Sylvester in 1893, first proved by Melchior
1940 and famously by Kelly via a minimal-distance argument) is a cornerstone of
combinatorial and incidence geometry. It seeds the Dirac–Motzkin conjecture on the number
of ordinary lines, connects to the Orchard problem, and generalizes to complex and
higher-dimensional settings (Kelly's theorem). Kelly's proof is a beautiful
extremal/minimal-counterexample argument and a genuinely non-trivial formalization
target: it exercises real-plane geometry, point–line incidence, and a discrete
minimization over a finite set.

## Known Results

### What's Already Proven

- Mathlib has `Collinear`, `AffineSubspace`, `affineSpan`, and point–line incidence via
  affine subspaces of `EuclideanSpace ℝ (Fin 2)`.
- Mathlib has the orthogonal-projection / perpendicular-distance API
  (`EuclideanGeometry.orthogonalProjection`, `Metric.infDist`) — the engine of Kelly's
  proof.
- Finiteness with `Finset.exists_min_image` / `Finset.min'` provides the minimal positive
  point–line distance that Kelly's argument minimizes over.

### What's Still Open

- No Lean formalization of the Sylvester–Gallai theorem exists in this gallery, and (to
  the best of the seeker's knowledge) it is not a named result in Mathlib.
- The crux step — showing the minimal point-to-(connecting-line) distance is realized by an
  *ordinary* line — has not been assembled in this repository.

### Our Goal

Formalize the Sylvester–Gallai theorem over `EuclideanSpace ℝ (Fin 2)` (or a real inner
product plane): for any finite, non-collinear point set, prove existence of a line
incident to exactly two points. Target Kelly's minimal-distance proof; a fallback is
Melchior's Euler-formula (projective duality) argument if the metric route stalls.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| picks-theorem | Planar point–line incidence and area reasoning | `Collinear`, affine geometry |
| morleys-theorem | Euclidean-triangle geometry in Mathlib | `EuclideanGeometry`, distances |
| cevas-theorem | Point–line incidence in the plane | affine/collinearity API |

## Initial Thoughts

### Potential Approaches

1. **Kelly's minimal-distance proof** (recommended): Among all pairs $(p, \ell)$ with
   $p \in S$, $\ell$ a line through $\ge 2$ points of $S$, and $p \notin \ell$, choose the
   pair minimizing $\mathrm{dist}(p, \ell) > 0$. Show this $\ell$ is ordinary: if it held a
   third point, two of the three points on $\ell$ would lie on the same side of the foot of
   the perpendicular from $p$, yielding a strictly smaller distance — contradiction.
   - Why it might work: the canonical short proof; reduces to a `Finset` minimization plus
     one planar-geometry inequality (foot-of-perpendicular ordering).
   - Risk: formalizing the "two of three on the same side of the foot" case analysis and the
     strict distance comparison in Mathlib's metric/projection API.

2. **Melchior's projective / Euler-formula proof**: dualize to an arrangement of lines and
   apply Euler's formula $V - E + F = 2$ to force a triangular face (ordinary point).
   - Why it might work: avoids metric inequalities; purely combinatorial once duality is set up.
   - Risk: needs projective-plane and planar-graph (Euler characteristic) infrastructure that
     is heavier to build in Lean.

### Key Difficulties

- Encoding "line through exactly two points" cleanly (a `Finset` filtered by membership in an
  `AffineSubspace`, with cardinality exactly 2).
- The minimal-distance extremal step: proving the chosen line is ordinary via the
  foot-of-perpendicular ordering argument, including the strict inequality giving the
  contradiction.

### What Would a Proof Need?

- Key lemma 1: existence of a minimizing pair $(p,\ell)$ with positive distance over the
  finite candidate set (`Finset.exists_min_image`).
- Key lemma 2 (crux): if a connecting line $\ell$ contains $\ge 3$ points of $S$, then for
  any $p \notin \ell$ there is a connecting line $\ell'$ and point $p'$ with
  $\mathrm{dist}(p',\ell') < \mathrm{dist}(p,\ell)$.
- Technical requirements: `EuclideanGeometry.orthogonalProjection`, `Metric.infDist`,
  `Collinear`, `affineSpan`, and `Finset` minimization.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematics is elementary but the formalization is substantial: Kelly's proof hinges
  on a geometric case analysis (ordering of three collinear points relative to a
  perpendicular foot) that must be made fully rigorous in Mathlib's metric API.
- No existing Mathlib named result to lean on; supporting incidence lemmas must be built.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks
- If hard: 3–4 weeks (if the foot-of-perpendicular case analysis resists `nlinarith`/`positivity`)

## References

### Papers
- J. J. Sylvester, *Mathematical Question 11851*, Educational Times (1893) — original conjecture.
- E. Melchior, *Über Vielseite der projektiven Ebene* (1940) — first proof via Euler's formula.
- L. M. Kelly's proof, popularized by Coxeter (1948); see Aigner & Ziegler, *Proofs from
  THE BOOK* — the minimal-distance argument.

### Online Resources
- Wikipedia, "Sylvester–Gallai theorem" — statement, Kelly's proof, generalizations.

### Mathlib
- `Mathlib.LinearAlgebra.AffineSpace.Collinear` — `Collinear`, affine span.
- `Mathlib.Geometry.Euclidean.Projection` / `orthogonalProjection` — distance to a line.
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` / `Metric.infDist` — point-to-set distance.
- `Mathlib.Data.Finset.Lattice` — `Finset.min'`, `Finset.exists_min_image`.

## Metadata

```yaml
tags:
  - combinatorial-geometry
  - incidence-geometry
  - euclidean-geometry
  - extremal-argument
related_proofs:
  - picks-theorem
  - morleys-theorem
difficulty: hard
source: seeker-selected
created: 2026-06-16
```
