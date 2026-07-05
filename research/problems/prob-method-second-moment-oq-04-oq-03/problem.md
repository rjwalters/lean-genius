# Problem: Weighted-Finset second-moment / Cantelli inequality

**Slug**: prob-method-second-moment-oq-04-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Replace the uniform counting measure `#s` by a weight function `w : α → ℝ≥0` (or `ℝ`) and prove
the second-moment / Cantelli-type bound with weighted sums `∑_{a} w(a) · (·)` in place of
cardinalities, e.g.

$$
\Big(\sum_a w(a)\, X(a)\Big)^2 \;\le\; \Big(\sum_a w(a)\Big)\Big(\sum_a w(a)\, X(a)^2\Big),
$$

and the corresponding one-sided concentration bound, all stated over `Finset`s without invoking
measure theory.

### Plain Language

The parent (`prob-method-second-moment-oq-04`) develops the second-moment method using the
uniform counting measure over a finite set (weights all `1`, so expectations are averages). This
child generalizes the measure to arbitrary nonnegative **weights** `w`, capturing non-uniform
discrete distributions — while deliberately staying in the elementary `Finset`/`BigOperators`
world (no `MeasureTheory` import). The weighted Cauchy–Schwarz and weighted Chebyshev/Cantelli
inequalities are the concrete targets.

### Why This Matters

The uniform version is the special case `w ≡ 1`. A weighted formulation makes the second-moment
method usable for non-uniform finite distributions (importance weights, biased sampling) while
keeping the measure-theory-free, computation-friendly style of the parent. It also cleanly
exhibits weighted Cauchy–Schwarz as the engine behind the method.

## Known Results

### What's Already Proven

- Parent `prob-method-second-moment-oq-04`: second-moment method over uniform counting measure.
- Mathlib `Finset.inner_mul_le_norm_mul_norm` / `Finset.sum_mul_sq_le_sq_mul_sq`
  (discrete Cauchy–Schwarz).
- Mathlib `Finset.sum` / `BigOperators` algebra.

### What's Still Open

- The weighted Cauchy–Schwarz packaging with a general weight `w`.
- The weighted one-sided (Cantelli) concentration bound as a corollary.
- Recovering the parent's uniform statements as the `w ≡ 1` special case.

### Our Goal

Prove the weighted discrete Cauchy–Schwarz inequality and the weighted Chebyshev/Cantelli
bound over a `Finset`, then instantiate `w ≡ 1` to recover the parent's results, confirming the
generalization is conservative.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| prob-method-second-moment-oq-04 | Direct parent; uniform second-moment method | Finset sums, Chebyshev |
| cauchy-schwarz | Underlying inequality (discrete form) | inner product / sum of squares |

## Initial Thoughts

### Potential Approaches

1. **Weighted Cauchy–Schwarz via `√w`**: apply Mathlib's discrete Cauchy–Schwarz to the
   sequences `√w·X` and `√w`, yielding the weighted inequality directly.
   - Why it might work: reduces the new result to an existing Mathlib lemma by reweighting.
   - Risk: `NNReal`/`Real` square-root bookkeeping and nonnegativity side goals.

2. **Direct SOS expansion**: prove `(∑ w X)² ≤ (∑ w)(∑ w X²)` by expanding
   `∑_{a,b} w(a)w(b)(X(a)−X(b))² ≥ 0`.
   - Why it might work: elementary, avoids square roots.
   - Risk: double-sum manipulation.

### Key Difficulties

- Nonnegativity hypotheses on `w` threaded through the concentration corollary.
- Defining weighted "mean" and "variance" so the Cantelli bound reads naturally.

### What Would a Proof Need?

- Key lemma 1: weighted discrete Cauchy–Schwarz `(∑ w X)² ≤ (∑ w)(∑ w X²)`.
- Key lemma 2: weighted Chebyshev ⇒ one-sided Cantelli bound.
- Technical requirements: `Finset.sum_mul_sq_le_sq_mul_sq`, `BigOperators`, nonneg lemmas.

## Tractability Assessment

**Difficulty**: Low-to-Medium

**Justification**:
- Discrete Cauchy–Schwarz is already in Mathlib; the generalization is a reweighting.
- The parent supplies the uniform template to mirror.
- Staying measure-theory-free keeps the dependency surface small.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days

## References

### Mathlib
- `Mathlib.Analysis.MeanInequalities` — discrete Cauchy–Schwarz / power-mean inequalities.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum` algebra.
- `Mathlib.Analysis.InnerProductSpace.Basic` — `sum_mul_sq_le_sq_mul_sq` style lemmas.

## Metadata

```yaml
tags:
  - probability
  - concentration
  - second-moment-method
  - cantelli
related_proofs:
  - prob-method-second-moment-oq-04
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
