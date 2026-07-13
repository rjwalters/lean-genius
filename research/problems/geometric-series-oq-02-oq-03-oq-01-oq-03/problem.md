# Problem: Neumann Series for (x − t)⁻¹ — Local Analyticity of Inversion

**Slug**: geometric-series-oq-02-oq-03-oq-01-oq-03
**Created**: 2026-07-04T00:45:01-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $R$ be a complete normed ring (Banach algebra) with unit. The parent proof
establishes the Neumann series for $(1 - t)^{-1} = \sum_{n \ge 0} t^n$ whenever
$\lVert t \rVert < 1$. Generalize to an **arbitrary unit** $x$ perturbed by $t$:

$$
(x - t)^{-1} = \sum_{n \ge 0} \left(x^{-1} t\right)^n x^{-1}
\qquad \text{whenever } x \in R^\times \text{ and } \lVert x^{-1} t \rVert < 1 .
$$

Equivalently, $x - t = x\,(1 - x^{-1}t)$ is a unit and its inverse is analytic in
$t$ on the open ball $\lVert x^{-1} t \rVert < 1$, giving **local analyticity of
inversion** on the open set of units $R^\times$.

### Plain Language

The parent result inverts $1 - t$ by a geometric (Neumann) series when $t$ is
small. This generalization says: near *any* invertible element $x$, the inverse
map $y \mapsto y^{-1}$ is given by a convergent power series in the perturbation
$t = x - y$. So inversion is not just continuous but real-analytic on the group
of units.

### Why This Matters

Local analyticity of inversion is the workhorse behind the openness of the unit
group, the holomorphic functional calculus, and perturbation theory for
operators. It upgrades the single-point Neumann series into a statement about
the whole open set $R^\times$.

## Known Results

### What's Already Proven

- Parent proof `geometric-series-oq-02-oq-03-oq-01`: Neumann series for
  $(1 - t)^{-1}$ with $\lVert t \rVert < 1$.
- Mathlib `NormedRing.inverse_add` / `Units.oneSub` / `Units.add` and
  `tsum_geometric_of_norm_lt_one`: the small-perturbation inverse and geometric
  summation are available.

### What's Still Open

- Packaging the general-unit statement as a named theorem in this entry's style,
  with the explicit series $\sum (x^{-1}t)^n x^{-1}$.
- The analyticity conclusion (continuity/Fréchet-differentiability of $y \mapsto
  y^{-1}$ at a general unit), if pursued beyond the summation identity.

### Our Goal

Prove the displayed identity for a general unit $x$ by reducing to the parent
case via the factorization $x - t = x(1 - x^{-1}t)$, and state local analyticity
of inversion as a corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| geometric-series-oq-02-oq-03-oq-01 | Direct parent — the $(1-t)^{-1}$ case | Neumann series, `tsum_geometric` |
| geometric-series | Base geometric series machinery | summable geometric series |

## Initial Thoughts

### Potential Approaches

1. **Factorization reduction** (primary): write $x - t = x(1 - x^{-1}t)$; since
   $x$ is a unit and $\lVert x^{-1}t\rVert < 1$, $1 - x^{-1}t$ is a unit by the
   parent result, so $x - t$ is a unit with inverse $(1 - x^{-1}t)^{-1} x^{-1}
   = \left(\sum (x^{-1}t)^n\right) x^{-1}$.
   - Why it might work: reuses the parent theorem verbatim; the algebra is a
     one-line factorization.
   - Risk: bookkeeping around left/right inverses in a non-commutative ring.

2. **Direct via Mathlib `Units`**: use `Units.add`/`NormedRing.inverse_add`
   to get the inverse, then identify it with the series.
   - Why it might work: Mathlib already has the openness of units.
   - Risk: matching Mathlib's `Ring.inverse` conventions to the explicit tsum.

### Key Difficulties

- Non-commutativity: keep the series factor $x^{-1}$ on the correct side.
- Converting between `Units R` and the `tsum` form cleanly.

### What Would a Proof Need?

- Lemma: $\lVert x^{-1}t\rVert < 1 \Rightarrow (1 - x^{-1}t) \in R^\times$
  (parent).
- Lemma: $(x - t) = x(1 - x^{-1}t)$ and inverse of a product of units.
- Summation: $(1 - x^{-1}t)^{-1} = \sum_n (x^{-1}t)^n$ (parent tsum).

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The parent theorem does the analytic heavy lifting; this is largely an
  algebraic reduction plus a summation rewrite.
- Mathlib's `NormedRing.inverse_add`, `Units`, and geometric-series lemmas are
  directly applicable.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days

## References

### Mathlib
- `Mathlib.Analysis.NormedSpace.Units` — `NormedRing.inverse_add`, openness of
  units, `Units.oneSub`.
- `Mathlib.Analysis.SpecificLimits.Normed` — `tsum_geometric_of_norm_lt_one`.

## Metadata

```yaml
tags:
  - analysis
  - neumann-series
  - normed-ring
  - banach-algebra
  - operator-inverse
  - perturbation-theory
related_proofs:
  - geometric-series-oq-02-oq-03-oq-01
  - geometric-series
difficulty: medium
source: gallery-gap
created: 2026-07-04T00:45:01-07:00
```

**Significance**: 6/10
**Tractability**: 6/10
