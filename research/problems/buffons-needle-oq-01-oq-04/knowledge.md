# Knowledge Base: buffons-needle-oq-01-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding (S1 OBSERVE, 2026-05-31)

This slug corresponds to the **4th `conclusion.openQuestion` of `buffons-needle-oq-01`** — generalizing the smooth-noodle theorem from 1-D C¹ curves to 2-D **convex bodies** (Buffon's coin, ellipses, polygons, etc.). The classical result (Laplace 1812, after Buffon 1733) is:

$$
\mathbb{E}[\#\text{crossings of } \partial K \text{ with line grid}] = \frac{2\,p}{\pi d}
\quad\text{where } p = \operatorname{perimeter}(K),\ d = \text{line spacing}.
$$

The **key structural insight** (S1, this memo): the result is **NOT new analytic content**. The bearer `BuffonsNeedleOQ01.buffon_smooth_of_contDiff` already proves exactly this formula for any C¹ planar curve — applied to the boundary curve $\partial K$, it gives the Buffon's coin formula immediately. The convexity hypothesis enters only in the *combinatorial* translation "boundary crossings = $2 \times $ (lines that cut $K$)" — a 10–15 LOC lemma about line/convex-set intersections.

This makes the slug **highly tractable** (Approach A: ~50–80 LOC corollary, no new axioms, no sorries).

---

## Insights

### S1: Bearer table at Mathlib v4.26.0 (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Bearer | Module | Role in S2 ACT |
|---|---|---|
| `BuffonsNeedleOQ01.buffon_smooth_of_contDiff` | `Proofs/BuffonsNeedleOQ01.lean` (line ~250 — main result) | **The core bearer**. Proves $\mathbb{E}[\text{crossings}] = 2 \cdot \operatorname{arcLength}(\gamma) / (\pi d)$ for any C¹ planar curve. S2 ACT is a one-line corollary applied to a closed C¹ boundary parametrisation. |
| `ContDiff` | `Mathlib.Analysis.Calculus.ContDiff.Defs` (canonical) | C¹ smoothness of $\partial K$. |
| `Convex.compact_iff_bounded` / `Convex.isClosed_*` | `Mathlib.Analysis.Convex.*` (canonical) | Compactness + closedness of convex body. |
| `MeasureTheory.intervalIntegrable` | `Mathlib.MeasureTheory.Integral.IntervalIntegral` (canonical) | Integrability of $\|\gamma'(t)\|$ over $[0, p]$. |

### S1: Translation lemma "boundary crossings = 2 × (lines that cut interior)"

For a compact convex body $K \subset \mathbb{R}^2$ and a line $\ell$:

* If $\ell \cap K = \emptyset$: boundary crossings = 0.
* If $\ell \cap \operatorname{interior}(K) = \emptyset$ but $\ell \cap K \ne \emptyset$: $\ell$ is a supporting line; intersects $\partial K$ in a *segment* (0-D for "generic" lines, but degenerate for tangent lines). Treated as crossings = 0 in a measure-zero set of orientations (negligible).
* If $\ell \cap \operatorname{interior}(K) \ne \emptyset$: by convexity, $\ell \cap K$ is a *non-degenerate segment*, and $\partial K \cap \ell = \{\text{the two endpoints of that segment}\}$. Boundary crossings = 2.

So $\mathbb{E}[\text{boundary crossings}] = 2 \cdot \mathbb{E}[\mathbb{1}_{\ell \text{ cuts } K}]$, and applying `buffon_smooth_of_contDiff` to $\partial K$ gives $\mathbb{E}[\text{boundary crossings}] = 2p / (\pi d)$, so $\mathbb{E}[\text{lines cutting }K] = p / (\pi d)$ — **Cauchy's formula**.

The Lean encoding of this translation needs:

* `Mathlib.Analysis.Convex.Combination` / `Mathlib.Analysis.Convex.Topology` — `Convex.segment_subset` and supporting-line API.
* `Set.ncard` (or `Finset.card` for a finite-fibre formulation) for counting boundary intersections.

No existing Mathlib lemma at v4.26.0 directly gives `|line ∩ ∂K| ≤ 2` for convex $K$. This 10–15 LOC lemma is the S2 ACT's only new analytic work.

### S1: Sibling-file overview

The `BuffonsNeedle*` chain is rich (11 files, 89+ theorems, 6 axioms total, 5 sorries — all in `OQ01OQ01`):

| File | LOC | Thms | Axioms | Sorries | Role |
|---|---|---|---|---|---|
| `BuffonsNeedle.lean` | 266 | 9 | 0 | 0 | Straight needle base case |
| `BuffonsNeedleOQ01.lean` | 250 | 11 | 0 | 0 | C¹ smooth noodle — **direct parent of this slug** |
| `BuffonsNeedleOQ01OQ01.lean` | 390 | 7 | 1 | 5 | Angular average (sub-theory) |
| `BuffonsNeedleOQ01OQ01OQ01.lean` | 223 | 7 | 1 | 0 | Sub-sub-theory |
| `BuffonsNeedleOQ01OQ01OQ04.lean` | 568 | 27 | 0 | 0 | **Different from this slug** — sibling at OQ01OQ01OQ04, not OQ01OQ04 |
| `BuffonsNeedleOQ01OQ01OQ04OQ01.lean` | 193 | 11 | 0 | 0 | Sub-theory of above |
| `BuffonsNeedleOQ01OQ02.lean` | 325 | 23 | 0 | 0 | Concrete C¹ parameterisations |
| `BuffonsNeedleOQ02.lean` | 262 | 14 | 0 | 0 | 3D Buffon |
| `BuffonsNeedleOQ02OQ01.lean` | 309 | 18 | 0 | 0 | 3D sub-theory |
| `BuffonsNeedleOQ02OQ02.lean` | 376 | 15 | 1 | 0 | 3D sub-theory |
| `BuffonsNeedleOQ02OQ03.lean` | 285 | 18 | 3 | 0 | 3D sub-theory |

**No existing `BuffonsNeedleOQ01OQ04.lean`** — S2 ACT creates this file fresh.

---

## Dead Ends

(None yet — S1 OBSERVE only.)

---

## Citations

* Buffon, G.-L. L. (1733). *Essai d'arithmétique morale.* — original 1-D needle problem.
* Laplace, P.-S. (1812). *Théorie analytique des probabilités.* — 2-D coin extension.
* Cauchy, A.-L. (1841). *Mémoire sur la rectification des courbes et la quadrature des surfaces courbes.* — perimeter = $\pi \times$ mean-width identity.
* Santaló, L. A. (1976). *Integral Geometry and Geometric Probability.* — modern reference for Cauchy-Crofton / mean-width formulas.
