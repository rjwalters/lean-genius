# Problem: From Rank-One to Finite-Rank — Projection onto a Subspace as a Sum of Rank-One Projectors

**Slug**: cauchy-schwarz-oq-01-oq-02-oq-01-oq-03
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ (an `RCLike` field) and let $E$ be an
inner product space over $\mathbb{K}$. Let $e : \mathrm{Fin}\,k \to E$ be an
**orthonormal family**, i.e. $\langle e_i, e_j\rangle = \delta_{ij}$, and let
$S = \operatorname{span}_{\mathbb{K}}(\operatorname{range} e)$ be the
$k$-dimensional subspace it spans. Write $P_S$ for the orthogonal projection onto
$S$. The claim is the finite-rank generalization of the parent's rank-one projector:

$$
P_S\,x \;=\; \sum_{i=1}^{k} \langle e_i, x\rangle \, e_i
\qquad\text{for every } x \in E,
$$

that is, $P_S$ is the **sum of the rank-one orthogonal projectors**
$x \mapsto \langle e_i, x\rangle\,e_i$ over the orthonormal family, together with the
**Parseval / Bessel equality on $S$**:

$$
\lVert P_S\,x\rVert^{2} \;=\; \sum_{i=1}^{k} \bigl\lvert \langle e_i, x\rangle\bigr\rvert^{2}
\qquad\text{for every } x \in E.
$$

For $k = 1$ (a single unit vector $e_0 = v/\lVert v\rVert$) both statements collapse to
the parent entry's rank-one facts $P_{\{v\}}x = \langle e_0,x\rangle\,e_0$ and
$\lVert P_{\{v\}}x\rVert = \lvert\langle e_0,x\rangle\rvert$.

A concrete Lean signature (real scalars shown; the file will be stated over an
arbitrary `RCLike` field) reads:

```lean
open scoped InnerProductSpace RealInnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Orthogonal projection onto the span of a finite orthonormal family equals the
    sum of the rank-one projectors over that family. -/
theorem orthogonalProjection_eq_sum_rank_one
    {k : ℕ} (e : Fin k → E) (he : Orthonormal 𝕜 e) (x : E) :
    (orthogonalProjection (Submodule.span 𝕜 (Set.range e)) x : E)
      = ∑ i, ⟪e i, x⟫_𝕜 • e i := by
  sorry

/-- Parseval / Bessel equality on the subspace: the squared norm of the projection
    is the sum of squared coordinate moduli. -/
theorem norm_orthogonalProjection_sq_eq_sum
    {k : ℕ} (e : Fin k → E) (he : Orthonormal 𝕜 e) (x : E) :
    ‖(orthogonalProjection (Submodule.span 𝕜 (Set.range e)) x : E)‖ ^ 2
      = ∑ i, ‖⟪e i, x⟫_𝕜‖ ^ 2 := by
  sorry
```

Equivalently, one packages the family as an `OrthonormalBasis (Fin k) 𝕜 S` for the
subspace `S` (a finite-dimensional inner product space) and uses
`OrthonormalBasis.sum_repr` transported back to `E` via the isometry `S ↪ E`.

### Plain Language

The parent proved that projecting a vector onto a single line is given by one simple
formula, $x \mapsto \langle e, x\rangle\,e$, and that this map is a genuine projector
(idempotent, complementary residual, exact norm). This problem asks the natural next
question: what if we project onto a whole $k$-dimensional subspace rather than a single
line? The answer is that the projection is just the **sum** of the one-line projections,
one for each vector in an orthonormal basis of the subspace:
$P_S x = \sum_i \langle e_i, x\rangle\,e_i$. Moreover the length-squared of the
projection is exactly the sum of the squares of the coordinates $|\langle e_i,x\rangle|^2$
— this is the finite-dimensional **Parseval identity** (equality form of **Bessel's
inequality**) restricted to the subspace $S$.

### Why This Matters

This is the exact step that turns the rank-one Gram–Schmidt/Cauchy–Schwarz picture into
the general theory of orthogonal projection. The sum-of-rank-one-projectors formula is
the operator identity $P_S = \sum_i e_i e_i^{*}$ (a finite-rank resolution-of-the-identity
statement), and the Parseval equality on $S$ is the sharp, attained form of Bessel's
inequality. Concretely, it is the analytic backbone of the **QR decomposition** and of
least-squares approximation: the best approximation of $x$ from $S$ is
$\sum_i \langle e_i, x\rangle\,e_i$, and its error norm is controlled by
$\lVert x\rVert^2 - \sum_i |\langle e_i,x\rangle|^2$. It closes the third open question
left by the parent entry ("Does the projector identity extend to projection onto a
finite-dimensional subspace, expressed as a sum of rank-one projectors over an orthonormal
basis?") and provides a reusable, fully verified bridge between Mathlib's
`orthogonalProjection` API and the coordinate/`OrthonormalBasis` API.

## Known Results

### What's Already Proven

- **One Gram–Schmidt step is an orthogonal projector** ($P = \mathrm{orthProj}\,v$ onto
  $\operatorname{span}\{v\}$: $P^2=P$, $(1-P)^2=1-P$, $P+(1-P)=\mathrm{id}$, exact norm
  $\lVert Px\rVert = \lvert\langle v,x\rangle\rvert/\lVert v\rVert$, $0$ axioms) — gallery
  entry `cauchy-schwarz-oq-01-oq-02-oq-01` (parent), the $k=1$ rank-one case of this
  problem.
- **Gram–Schmidt via Cauchy–Schwarz** (boundedness of the projection coefficient,
  orthogonal residual, Pythagoras) — gallery entry `cauchy-schwarz-oq-01-oq-02`
  (grandparent).
- **Mathlib orthogonal projection API.** `orthogonalProjection (K : Submodule 𝕜 E)` for a
  complete subspace `K`, with `orthogonalProjection_mem`, `orthogonalProjection_inner_eq_zero`
  (the defining orthogonality of the residual), `orthogonalProjection_eq_self_iff`, and
  `inner_orthogonalProjection_eq_of_mem_right` / `_left` — in
  `Mathlib.Analysis.InnerProductSpace.Projection`.
- **Orthonormal-basis coordinate expansion.** `OrthonormalBasis.sum_repr`
  ($x = \sum_i \langle b_i,x\rangle\,b_i$ over a full basis) and
  `Orthonormal.inner_products` in `Mathlib.Analysis.InnerProductSpace.PiL2`.
- **Bessel's inequality** `Orthonormal.sum_inner_products_le`
  ($\sum_i |\langle e_i,x\rangle|^2 \le \lVert x\rVert^2$) and
  `Orthonormal.inner_products_le` in `Mathlib.Analysis.InnerProductSpace.Basic`.

### What's Still Open

- No gallery entry assembles the **sum-of-rank-one-projectors** identity
  $P_S x = \sum_i \langle e_i,x\rangle\,e_i$ for a finite orthonormal family in an
  ambient space $E$ (as opposed to the full-space `OrthonormalBasis.sum_repr`).
- No gallery entry states the **Parseval equality on the subspace**
  $\lVert P_S x\rVert^2 = \sum_i |\langle e_i,x\rangle|^2$ as the attained case of Bessel
  restricted to $S$ (Mathlib has the inequality, not this subspace-equality packaging).
- The clean reduction to the parent's $k=1$ rank-one statement, exhibiting the parent as
  the one-term sum.

### Our Goal

Produce a `0`-axiom, `0`-sorry Lean file that proves, over an arbitrary `RCLike` field:
(1) $P_S x = \sum_i \langle e_i, x\rangle\,e_i$ where $S = \operatorname{span}(\mathrm{range}\,e)$;
(2) $\lVert P_S x\rVert^2 = \sum_i |\langle e_i,x\rangle|^2$;
(3) the residual $x - P_S x$ is orthogonal to every $e_i$ (hence to $S$);
(4) idempotency $P_S(P_S x) = P_S x$ on $S$ and reconstruction $P_S + (1 - P_S) = \mathrm{id}$;
and (5) the $k=1$ specialization recovering the parent. The subspace $S$ is
finite-dimensional, hence complete, so `orthogonalProjection` is well defined without any
completeness hypothesis on $E$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-schwarz-oq-01-oq-02-oq-01 | Direct parent: rank-one ($k=1$) projector onto a line; this problem sums $k$ of them | `inner_smul_right`, `div_self`, idempotency, exact norm |
| cauchy-schwarz-oq-01-oq-02 | Grandparent: Gram–Schmidt via Cauchy–Schwarz (bound, residual, Pythagoras) | Cauchy–Schwarz, orthogonal residual |
| cauchy-schwarz | Base inner-product inequality underlying Bessel/Parseval | `norm_inner_le_norm`, inner-product algebra |

## Initial Thoughts

### Potential Approaches

1. **Approach A — `OrthonormalBasis` of the subspace $S$ (recommended idiomatic route).**
   The family $e$ restricts to an orthonormal basis of $S = \operatorname{span}(\mathrm{range}\,e)$.
   Build `b : OrthonormalBasis (Fin k) 𝕜 S` from `he` and the span construction, use
   `OrthonormalBasis.sum_repr` inside $S$ to expand
   $P_S x = \sum_i \langle b_i, P_S x\rangle\,b_i$, and rewrite
   $\langle b_i, P_S x\rangle = \langle e_i, x\rangle$ using the residual orthogonality of
   the projector (a lemma of the form `inner_orthogonalProjection_eq_of_mem_left`, since
   $e_i \in S$). Transport along the isometry `S ↪ E` (`Submodule.subtypeₗᵢ`) to land the
   sum in $E$. Parseval then follows from the orthonormal `norm_sum` computation.
   - Why it might work: every ingredient is a named Mathlib lemma; the work is glue and
     the $S \hookrightarrow E$ transport.
   - Risk: bookkeeping between $E$-inner-products and $S$-inner-products; managing the
     isometry coercion cleanly.

2. **Approach B — Direct verification via the projection characterization (recommended for a self-contained file).**
   Define $Q x := \sum_i \langle e_i, x\rangle\,e_i$ directly and prove
   $Q x = P_S x$ using the uniqueness of orthogonal projection: show
   (i) $Q x \in S$ (a sum of scalar multiples of the $e_i$), and
   (ii) $x - Q x \perp e_j$ for all $j$, i.e. $\langle e_j, x - Q x\rangle = 0$, which by
   orthonormality is $\langle e_j, x\rangle - \sum_i \langle e_i,x\rangle\langle e_j,e_i\rangle
   = \langle e_j,x\rangle - \langle e_j,x\rangle = 0$. Then invoke a uniqueness lemma of the
   form `eq_orthogonalProjection_of_mem_of_inner_eq_zero` ("if $y \in K$ and $x - y \perp K$
   then $y = P_K x$").
   - Why it might work: avoids the $S \hookrightarrow E$ transport entirely; the residual
     computation is a one-line `Finset.sum` manipulation using $\langle e_i,e_j\rangle=\delta_{ij}$.
   - Risk: need to supply orthogonality against all of $S$ (spanning suffices via linearity),
     and the Parseval norm still needs the orthonormal `norm_sum` computation.

Approach B is likely the cleaner path to a self-contained `0`-axiom file, mirroring the
parent's direct style; Approach A is the more idiomatic "assemble existing API" route.

### Key Difficulties

- **Two inner-product worlds.** `orthogonalProjection` has values in the subspace `↥S`, so
  statements comparing $P_S x$ (an element of $E$ after coercion) with a sum in $E$ require
  careful handling of the `Submodule.subtype` coercion and possibly `OrthonormalBasis`
  transport.
- **Orthogonality against a span.** The residual must be shown orthogonal to all of $S$,
  not just to each $e_i$; use that orthogonality to a spanning set extends by linearity
  (a lemma of the form `Submodule.inner_right_of_mem_span`, or reduce via `Submodule.span_induction`).
- **Parseval cross terms.** Expanding $\lVert \sum_i c_i e_i\rVert^2 = \langle \sum_i c_i e_i,
  \sum_j c_j e_j\rangle$ into $\sum_{i,j} \overline{c_i} c_j \langle e_i, e_j\rangle$ and
  collapsing the double sum to the diagonal via $\langle e_i,e_j\rangle = \delta_{ij}$
  (`inner_sum`, `sum_inner`, `Finset.sum_ite_eq`, `Orthonormal`); the standard but slightly
  fiddly orthonormal `norm_sum` computation.
- **`RCLike` vs `ℝ`.** Over $\mathbb{C}$ the coefficients are $\langle e_i, x\rangle \in
  \mathbb{C}$ and the squared modulus is $\lVert\langle e_i,x\rangle\rVert^2$; keep the
  statement `RCLike`-general as the parent did.

### What Would a Proof Need?

- Key lemma 1: $x - \sum_i \langle e_i,x\rangle\,e_i \perp e_j$ for every $j$
  (residual orthogonality), from orthonormality and `Finset` linearity of the inner product.
- Key lemma 2: $\sum_i \langle e_i,x\rangle\,e_i \in S = \operatorname{span}(\mathrm{range}\,e)$.
- Key lemma 3: uniqueness of orthogonal projection
  (`eq_orthogonalProjection_of_mem_of_inner_eq_zero`-style) to identify the sum with $P_S x$.
- Key lemma 4: orthonormal `norm_sum`,
  $\lVert \sum_i c_i e_i\rVert^2 = \sum_i \lVert c_i\rVert^2$, for the Parseval equality.
- Technical requirements: finite-dimensionality of $S$ (so `orthogonalProjection` exists),
  the `S ↪ E` isometry if following Approach A, and `Finset.sum`/`Fintype` bookkeeping.

## Tractability Assessment

**Difficulty**: Moderate-High (assembly of existing Mathlib projection/orthonormal API)

**Justification**:
- The result is a **standard, fully classical theorem** (finite-dimensional Parseval /
  resolution of the identity) with **substantial Mathlib support already in place**:
  `orthogonalProjection`, `Orthonormal`, `OrthonormalBasis.sum_repr`,
  `Orthonormal.sum_inner_products_le` (Bessel). The main work is *assembly* and the
  sum-of-projectors bookkeeping, not new mathematics.
- The **residual-orthogonality + uniqueness** route (Approach B) is a direct, low-risk port
  of the parent's style to a `Finset.sum` of terms and is very likely to close with
  `0` axioms.
- The only genuine friction is the coercion/transport between the ambient space $E$ and the
  subspace $S = \uparrow(\operatorname{span}\,e)$, and the orthonormal `norm_sum`
  double-sum collapse — both are exercised elsewhere in Mathlib.
- Similar solved work: the parent rank-one entry (this is its $k$-fold sum) and Mathlib's
  own `OrthonormalBasis` expansion lemmas demonstrate the toolkit end-to-end.

**Estimated Effort**:
- Exploration: 0.5–1 day (choose Approach A vs B; confirm the exact
  `eq_orthogonalProjection_of_mem_of_inner_eq_zero` and orthonormal `norm_sum` lemma names).
- If tractable (expected): 1–3 days for a `0`-axiom file with the sum-of-projectors
  identity, the Parseval equality, residual orthogonality, idempotency, and the $k=1$
  recovery of the parent.

## References

### Books
- Conway, J. B., *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990 —
  orthogonal projections, orthonormal bases, Bessel's inequality and Parseval's identity
  (Chapter I).
- Halmos, P. R., *Finite-Dimensional Vector Spaces*, 2nd ed., Springer, 1958 — orthogonal
  projection onto a subspace, resolution of the identity, and the projector calculus in
  finite dimension.
- Axler, S., *Linear Algebra Done Right*, 3rd ed., Springer, 2015 — orthonormal bases,
  orthogonal projections, and best approximation (least squares).

### Online Resources
- https://en.wikipedia.org/wiki/Parseval%27s_identity — Parseval / Bessel equality.
- https://en.wikipedia.org/wiki/Projection_(linear_algebra) — orthogonal projection as a
  sum of rank-one projectors.

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Projection` — `orthogonalProjection`,
  `orthogonalProjection_inner_eq_zero`, `orthogonalProjection_mem`, and a uniqueness lemma
  of the form `eq_orthogonalProjection_of_mem_of_inner_eq_zero`.
- `Mathlib.Analysis.InnerProductSpace.PiL2` — `OrthonormalBasis`, `OrthonormalBasis.sum_repr`,
  and orthonormal-basis coordinate/projection expansions.
- `Mathlib.Analysis.InnerProductSpace.Basic` — `Orthonormal`, `Orthonormal.inner_products`,
  `Orthonormal.sum_inner_products_le` (Bessel's inequality), `inner_sum`, `sum_inner`.
- `Mathlib.LinearAlgebra.Span` — `Submodule.span`, `Submodule.mem_span_range` and
  span-induction principles for extending orthogonality from a spanning set to all of $S$.

## Metadata

```yaml
tags:
  - linear-algebra
  - inner-product-spaces
  - orthogonal-projection
  - parseval
  - bessel
  - gram-schmidt
related_proofs:
  - cauchy-schwarz-oq-01-oq-02-oq-01
  - cauchy-schwarz-oq-01-oq-02
  - cauchy-schwarz
difficulty: moderate-high
source: gallery-gap
created: 2026-06-30
```
