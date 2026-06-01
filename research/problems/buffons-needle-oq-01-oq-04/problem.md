# Problem: Buffon's Coin and the Cauchy Mean-Width Generalization

**Slug**: buffons-needle-oq-01-oq-04
**Created**: 2026-04-05T19:30:47-07:00
**Status**: Active (S1 OBSERVE complete 2026-05-31)
**Source**: gallery-gap (4th open question of `buffons-needle-oq-01`)

## Problem Statement

### Formal Statement

Let $K \subset \mathbb{R}^2$ be a (compact, convex) plane region with rectifiable boundary $\partial K$ of perimeter $p$. Drop $K$ uniformly at random onto an infinite family of parallel lines spaced $d > 0$ apart. Then the expected number of crossings of $\partial K$ with these parallel lines is

$$
\mathbb{E}\bigl[\#\{\text{crossings of } \partial K\text{ with the line grid}\}\bigr]
\;=\; \frac{p}{\pi d / 2}
\;=\; \frac{2\,p}{\pi d}.
$$

Equivalently, the expected number of parallel lines that *cut* $K$ (i.e. intersect $\partial K$ in at least one point) is $p / (\pi d)$, since each line cuts a convex body's boundary in either $0$ or $2$ points.

### Plain Language

This is **Buffon's coin problem** (Laplace 1812 extended Buffon's 1733 needle): instead of a 1-D needle of length $\ell$ (where $\mathbb{P}[\text{crossing}] = 2\ell / (\pi d)$ for $\ell \le d$), drop a 2-D convex object — a coin, an ellipse, a triangle, any convex set $K$ with perimeter $p$. The expected number of times its **boundary** intersects the line grid depends only on the perimeter $p$, not on the shape. This is a special case of **Cauchy's formula for mean width**, which says that the average projection length of a convex body onto a random line equals $p / \pi$.

### Why This Matters

* **Bridges classical integral geometry with measure theory.** Cauchy's formula and the broader Crofton/Cauchy-Crofton framework are the natural ℝ² generalization of Buffon's needle, and Mathlib v4.26.0 has both the measure-theory primitives and the C¹-arc-length machinery this proof needs. A clean Lean formalization closes a 200-year-old gallery gap.
* **Reuses the smooth-noodle theorem.** `BuffonsNeedleOQ01.lean`'s main theorem `buffon_smooth_of_contDiff` — which proves $\mathbb{E}[\text{crossings}] = 2 \cdot \operatorname{arcLength}(\gamma) / (\pi d)$ for any C¹ planar curve — is *already exactly the right statement* for the convex-body case, applied to the boundary curve $\partial K$. The Buffon's coin formula is a one-step corollary: parametrise $\partial K$ as a C¹ closed curve (when $K$ is C¹-smooth) and plug into `buffon_smooth_of_contDiff`.
* **Direction-of-travel for the Cauchy-Crofton open question.** The parent file's 4-item `openQuestions` list cites (i) "Full Cauchy-Crofton formula for arbitrary measures on lines in ℝ²", (ii) higher-dim hyperplane arrangements, (iii) Lipschitz curves, (iv) **this** convex-body generalization. Items (i) and (ii) require substantially more new Mathlib infrastructure (random-line measures, ℝⁿ angular slicing); item (iv) is the most tractable because it reuses existing chain machinery.

## Known Results

### What's Already Proven

* **`BuffonsNeedle.lean`** (266 LOC, 9 theorems, 0 axioms, 0 sorries) — Buffon's needle for the straight 1-D needle: $\mathbb{P}[\text{cross}] = 2\ell/(\pi d)$ for $\ell \le d$. The base case.
* **`BuffonsNeedleOQ01.lean`** (250 LOC, 11 theorems, 0 axioms, 0 sorries) — **Buffon-Barbier "smooth noodle" theorem** for C¹ planar curves. `buffon_smooth_of_contDiff (γ : ℝ → ℝ × ℝ) (a b : ℝ) (d : ℝ) (hd : 0 < d) (hγ : ContDiff ℝ 1 γ) : E[crossings on [a, b]] = 2 * arcLength(γ, a, b) / (π * d)`. **Load-bearing**: this is the bearer for the OQ-04 reduction.
* **`BuffonsNeedleOQ01OQ01.lean`** (390 LOC, 7 theorems, 1 axiom, 5 sorries) — angular-average lemma underlying the smooth-noodle reduction. Axiomatised step still present.
* Mathlib v4.26.0:
  * `Mathlib.MeasureTheory.Constructions.Pi` — product measures (uniform on rotation × translation).
  * `Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts` — Fubini for line-integrals; relevant for the Cauchy mean-width computation.
  * `Mathlib.Geometry.Manifold.IntegralCurve.*` — C¹ curves on manifolds (overkill for ℝ², but the API surface is available).
  * `Mathlib.MeasureTheory.Function.Jacobian` — change of variables; needed for the convex-body shape-independence step.
  * **NOT yet in Mathlib**: a `Convex.perimeter` definition or a `Convex.cauchy_meanWidth` theorem. The intended formalization here introduces only the *Buffon* aspect, not the abstract convex-perimeter theory.

### What's Still Open

* The four `conclusion.openQuestions` of the parent `buffons-needle-oq-01`:
  1. **Full Cauchy-Crofton formula** for arbitrary measures on lines in ℝ² — *not this slug; needs a random-line-measure infrastructure that does not yet exist in Mathlib*.
  2. **Higher-dimensional versions** (hyperplane arrangements in ℝⁿ) — *not this slug; downstream of (1)*.
  3. **Extension to Lipschitz curves** — *not this slug; would need a Lipschitz-arc-length API*.
  4. **Connection to Buffon's coin** — **this slug**.

### Our Goal

**S2 ACT (recommended)**: create a new file `proofs/Proofs/BuffonsNeedleOQ01OQ04.lean` proving Buffon's coin for **C¹-smooth convex bodies** by reducing to `buffon_smooth_of_contDiff`. Concretely:

```lean
-- New theorem in BuffonsNeedleOQ01OQ04.lean
theorem buffon_coin_smooth (γ : ℝ → ℝ × ℝ) (a b : ℝ) (hab : a ≤ b)
    (d : ℝ) (hd : 0 < d) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ a = γ b) (hconvex : ConvexHull ℝ (Set.range (γ ∘ Set.uIcc a b)) = ...) :
    E[boundary crossings] = 2 * perimeter(K) / (π * d) := by
  exact buffon_smooth_of_contDiff γ a b d hd hγ
```

The convexity hypothesis enters only to ensure the "boundary crossings = 2 × line-cuts" half-translation, which is a *combinatorial* observation, not an analytic one. The C¹ + closed-curve hypotheses are exactly what `buffon_smooth_of_contDiff` needs.

**Estimated effort**: ~50–80 LOC of new Lean (the bulk is the convexity-to-line-cuts translation; the core probability statement is a one-line corollary). 0 new axioms, 0 sorries.

**Alternative S2 candidates** (less tractable):

* **(B) Strict Buffon's coin** for a disk of radius $r \le d/2$ — a *direct* probability computation rather than a corollary of the smooth noodle theorem. ~30–40 LOC; more pedagogically classic but mathematically less interesting (it's a special case of the general result).
* **(C) Cauchy mean-width formula** for general convex bodies — would require defining `Convex.perimeter` and `Convex.meanWidth` and proving Cauchy's identity. ~150–250 LOC, requires substantial new Mathlib infrastructure on convex bodies. Out-of-scope for an S2 ACT; better as a multi-iteration sub-chain.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `buffons-needle` | Straight 1-D needle base case ($P = 2\ell/(\pi d)$); the base case from which all generalizations descend. | Uniform measure on $[0, d/2] \times [0, \pi/2]$, indicator integral. |
| `buffons-needle-oq-01` | C¹ smooth-noodle theorem; the **direct parent**. `buffon_smooth_of_contDiff` is the bearer used by S2 ACT. | C¹ arc-length, angular averaging, Fubini, `IntervalIntegrable` from `ContDiff`. |
| `buffons-needle-oq-01-oq-01` | Angular-average lemma underlying the smooth-noodle reduction (1 axiom, 5 sorries). | Polar coordinates, dominated convergence. |
| `buffons-needle-oq-01-oq-02` | Smooth Buffon for explicit needle parameterisations (325 LOC, 23 theorems, 0 axioms). | Concrete C¹ curves, explicit arc-length formulas. |
| `buffons-needle-oq-02` | 3D Buffon (needle in space, parallel-plane grid). Independent direction. | Spatial measure, mean-width-3D analogue. |
| `buffons-needle-oq-01-oq-01-oq-04` | Pre-existing OQ-01-OQ-01-OQ-04 file (568 LOC, 27 theorems). **NOT the same as this slug** — this slug is OQ-01-OQ-04, a direct child of OQ-01. | unrelated parameterisation work |

## Initial Thoughts

### Potential Approaches

1. **Approach A (recommended): Smooth-boundary reduction.** Parametrise $\partial K$ for a C¹-smooth convex body $K$ as a closed C¹ curve $\gamma : [0, p] \to \mathbb{R}^2$, then apply `buffon_smooth_of_contDiff` directly. The convexity hypothesis enters only when translating from "boundary crossings" to "lines that cut $K$" (factor of 2). ~50–80 LOC.
   * Why it works: `buffon_smooth_of_contDiff` is already proved for any C¹ curve; closed-ness is not needed for the formula.
   * Risk: low. The reduction is structural; the analytic content is reused.

2. **Approach B: Direct coin computation.** For $K = $ closed disk of radius $r$, compute the probability of crossing directly. ~30 LOC; simpler but less general.

3. **Approach C: Cauchy mean-width formula.** Build the full Cauchy identity for general convex bodies. ~150–250 LOC; requires substantial new Mathlib infrastructure on convex bodies. Out-of-scope.

### Key Difficulties

* **Convexity-to-line-cuts translation** (Approach A): for a convex body $K$, "boundary crosses a parallel line $\ell$" happens at most twice. Proving this in Lean requires `Convex.isClosed_le_of_left` / `Convex.interior_intersection` style API; check for `Convex.line_intersection_cardinality_le_two` or similar.
* **Closed-curve parameterisation**: the formula needs a *closed* C¹ curve. The bearer `buffon_smooth_of_contDiff` does NOT require closure, so this is purely a perimeter-naming step — the closed-ness gives $\int_a^b |\gamma'(t)| dt = \operatorname{perimeter}(\partial K)$.

### What Would a Proof Need?

* **Key lemma 1** (convex-body boundary crossings): for $K \subset \mathbb{R}^2$ convex compact and $\ell$ a line, $|\partial K \cap \ell| \in \{0, 1, 2\}$, with $|\partial K \cap \ell| = 2$ iff $\ell \cap \operatorname{interior}(K) \ne \emptyset$. ~20 LOC, Mathlib `Convex.*` API.
* **Key lemma 2** (perimeter = arcLength of closed C¹ boundary): if $\gamma : [a, b] \to \partial K$ is a C¹ parametrisation of $\partial K$ with $\gamma(a) = \gamma(b)$, then $\int_a^b \|\gamma'(t)\| dt = \operatorname{perimeter}(\partial K)$. ~10 LOC, definitional.
* **Buffon coin theorem** (corollary): apply `buffon_smooth_of_contDiff`. ~5 LOC.
* **Technical requirements**: C¹ smoothness of $\partial K$ is a *strong* hypothesis — polygons, the L¹ ball, the unit square fall outside. The result extends to rectifiable boundaries via the C¹ approximation argument, but that's the deferred Lipschitz extension (open question (iii) of the parent).

## Tractability Assessment

**Difficulty**: **Low** for Approach A (recommended); Medium for Approach B (direct coin); High for Approach C (full Cauchy mean-width).

**Justification**:

* **Approach A is essentially a corollary of an existing 0-axiom-0-sorry theorem.** The bearer `buffon_smooth_of_contDiff` does all the heavy analytic lifting; this slug just wraps it with the convexity translation.
* **Similar work has been done in the chain.** `BuffonsNeedleOQ01OQ02.lean` (325 LOC, 23 theorems, 0 axioms) is a parallel "concrete-cases" sibling — same pattern of "apply the smooth-noodle bearer to a specific curve family", just with different curve families.
* **No Mathlib gaps blocking Approach A.** `Convex.compact_*`, `IsClosed.convexHull`, `ContDiff` are all v4.26.0-stable. The convexity-to-line-cuts translation may need a hand-rolled 10–15 LOC lemma (Mathlib's `Convex.*` API on line intersections is sparse), but no missing infrastructure.

**Estimated Effort**:

* Exploration (S1 OBSERVE — this memo): **done, ~1 hour**.
* S2 ACT (Approach A): **~3-4 hours** (50–80 LOC + state.md + meta.json + Docker verify).
* S3+ (extensions to Lipschitz boundaries, Cauchy mean-width): **deferred**, separate slugs.
