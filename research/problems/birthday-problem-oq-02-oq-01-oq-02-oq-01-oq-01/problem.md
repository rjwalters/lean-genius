# Problem: Schur-convexity of Σ pᵢ² — globalizing the birthday-collision smoothing step

**Slug**: birthday-problem-oq-02-oq-01-oq-02-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For probability vectors `p, q` on a finite type (`pᵢ ≥ 0`, `Σ pᵢ = 1`):
$$
p \preceq q \ (\text{$p$ majorized by $q$}) \quad\Longrightarrow\quad \sum_i p_i^2 \ \le\ \sum_i q_i^2,
$$
i.e. `Σ (·)²` is Schur-convex; the uniform vector (minimizer) and a point-mass (maximizer) are the two endpoints of the majorization order.

### Plain Language

The parent bounds the birthday-collision probability and isolates a *local* smoothing lemma `smoothing_sum_sq_le`: moving probability mass to make a distribution "more even" (a Robin-Hood / `T`-transform) does not increase `Σ pᵢ²`. This leaf globalizes that one step into the full statement: whenever `p` is majorized by `q`, the sum of squares of `p` is at most that of `q`. That single inequality simultaneously yields the parent's minimum (uniform distribution minimizes collision probability) and this entry's maximum (concentration maximizes it).

### Why This Matters

`Σ pᵢ²` is the collision probability; its monotonicity under majorization is the structural reason the uniform distribution is the unique collision minimizer and a point mass the maximizer. Promoting a local smoothing step to a global Schur-convexity statement is the canonical "robin-hood ⇒ majorization" upgrade, and gives a clean, reusable extremal principle rather than a problem-specific bound.

## Known Results

### What's Already Proven

- Parent `birthday-problem-oq-02-oq-01-oq-02-oq-01`: sharp upper bound on collision probability and the local smoothing lemma `smoothing_sum_sq_le`.
- Mathlib: majorization API where available (`Finset` sorting, `MonovaryOn`/rearrangement, `inner_le_nnorm`), `Finset.sum`, convexity (`ConvexOn`), `Finset.inner_mul_le_norm_mul_norm`.

### What's Still Open

- The global step: `p ≼ q ⇒ Σ pᵢ² ≤ Σ qᵢ²`, assembled from the local smoothing move.

### Our Goal

State majorization `p ≼ q` (partial sums of the decreasing rearrangement), then prove `Σ pᵢ² ≤ Σ qᵢ²` by realizing `p` from `q` through finitely many smoothing (`T`-transform) steps — each covered by the parent's `smoothing_sum_sq_le` — or directly via the Schur-convexity criterion for the symmetric convex function `x ↦ x²`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `birthday-problem-oq-02-oq-01-oq-02-oq-01` | parent: collision bound + local smoothing | sum of squares, smoothing step |
| `birthday-problem` | base collision-probability problem | counting, probability |
| `amgm-inequality` family | convexity / extremal sums | Jensen, rearrangement |

## Initial Thoughts

### Potential Approaches

1. **Muirhead / T-transform chain**: use that `p ≼ q` iff `p` is obtained from `q` by finitely many Robin-Hood transfers; apply `smoothing_sum_sq_le` along the chain and telescope.
   - Why it might work: directly reuses the parent's verified local step; only the "majorization ⇒ finite chain of transfers" lemma is new.
   - Risk: formalizing the finite-transfer decomposition of majorization may be heavy if Mathlib lacks it.

2. **Schur-convexity criterion**: invoke (or prove) that a symmetric convex `f` makes `Σ f(pᵢ)` Schur-convex, instantiated at `f = (·)²`.
   - Why it might work: `x²` is convex and symmetric; if Mathlib has the criterion, it is a one-step application.
   - Risk: Mathlib's majorization/Schur-convexity coverage is partial; may need to build the criterion.

### Key Difficulties

- Choosing/building the majorization definition that best matches available Mathlib lemmas.
- The transfer-decomposition lemma if going the T-transform route.

### What Would a Proof Need?

- Key lemma 1: a usable majorization predicate (partial-sum form).
- Key lemma 2: majorization ⇒ chain of smoothing transfers (or the Schur-convexity criterion).
- Key lemma 3: telescoping `smoothing_sum_sq_le` to the global inequality, recovering uniform-min and point-mass-max as endpoints.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The local step is already verified in the parent (0-axiom).
- The remaining work is a standard majorization upgrade; difficulty depends on Mathlib's majorization API maturity.
- Endpoints (uniform / point mass) drop out once the global inequality holds.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–5 days
- If hard: building majorization/Schur-convexity scaffolding from scratch

## References

### Papers
- A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its Applications* — Schur-convexity, T-transforms.

### Online Resources
- Standard references on majorization and Schur-convex functions.

### Mathlib
- `Mathlib/Analysis/Convex/...` — convexity, Jensen.
- `Mathlib/Order/...` and rearrangement/`MonovaryOn` lemmas for majorization-style arguments.

## Metadata

```yaml
tags:
  - probability
  - birthday-problem
  - schur-convexity
  - majorization
  - collision-probability
related_proofs:
  - birthday-problem-oq-02-oq-01-oq-02-oq-01
  - birthday-problem
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
