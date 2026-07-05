# Problem: Power means across the cross-zero regime

**Slug**: cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01-oq-01-oq-01-oq-01
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
r < 0 < t \implies M_r(x) \le M_0(x) \le M_t(x)
$$

where $M_p(x) = \left(\tfrac1n\sum_i x_i^p\right)^{1/p}$ for $p \ne 0$ and $M_0(x) = \left(\prod_i x_i\right)^{1/n}$ is the geometric mean, for positive reals $x_i > 0$.

### Plain Language

The generalized (power / Hölder) mean $M_p$ is monotone increasing in the exponent $p$. The parent entry established monotonicity for exponents of the same sign using reciprocal duality $M_{-p}(x) = 1/M_p(1/x)$. That duality maps a positive exponent to a negative one but cannot bridge an interval that straddles $0$. This problem closes the gap: prove $M_r \le M_t$ whenever $r < 0 < t$ by bridging through the geometric mean $M_0$.

### Why This Matters

Completing the sign-crossing case yields full monotonicity of power means over all of $\mathbb{R} \cup \{0\}$, which subsumes AM–GM, GM–HM, and the QM–AM chain as special evaluations. It is the last structural gap in the power-mean hierarchy for this gallery line.

## Known Results

### What's Already Proven

- Same-sign monotonicity $M_p \le M_q$ for $0 < p \le q$ (parent entry, via Jensen / Hölder).
- Reciprocal duality $M_{-p}(x) = M_p(x^{-1})^{-1}$ (parent entry).
- AM–GM: $M_0 \le M_1$ (gallery AM–GM family).

### What's Still Open

- The cross-zero comparison $M_r \le M_t$ for $r < 0 < t$.
- A uniform statement valid at the removable singularity $p = 0$ (continuity of $p \mapsto M_p$).

### Our Goal

Prove the two bridging inequalities $M_r(x) \le M_0(x)$ (for $r < 0$) and $M_0(x) \le M_t(x)$ (for $t > 0$), then chain them. The right half is generalized AM–GM; the left half follows by applying it to $x^{-1}$ and inverting.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-schwarz-integral parent chain | same power-mean hierarchy | Jensen, Hölder duality |
| jensen-inequality | convexity engine for the GM bound | Jensen's inequality |

## Initial Thoughts

### Potential Approaches

1. **Bridge via geometric mean**: prove $M_0 \le M_t$ by Jensen on $\log$, then get $M_r \le M_0$ by the reciprocal-duality trick applied to the just-proved inequality.
   - Why it might work: both halves are known-shaped inequalities; only the gluing is new.
   - Risk: Mathlib geometric-mean API phrasing may not line up cleanly.

2. **Direct weighted Jensen** on the convex function $u \mapsto u^{t/r}$ across the sign change.
   - Why it might work: single Jensen application.
   - Risk: convexity direction flips with the sign of the exponent ratio; bookkeeping-heavy.

### Key Difficulties

- Handling $M_0$ as the removable point rather than an $M_p$ instance.
- Mathlib API for the geometric mean of a Finset (`Finset.prod`, `Real.rpow`).

### What Would a Proof Need?

- Key lemma 1: $M_0(x) \le M_t(x)$ for $t > 0$ (generalized AM–GM).
- Key lemma 2: $M_r(x) \le M_0(x)$ for $r < 0$ via $x \mapsto x^{-1}$.
- Technical requirements: `Real.rpow`, weighted AM–GM, geometric-mean monotonicity lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Both bridging halves are standard and the GM bound already exists in the gallery AM–GM line.
- The novelty is purely the sign-crossing glue, a short chaining argument.
- Mathlib provides weighted AM–GM and `Real.rpow` monotonicity lemmas.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 2–4 days
- If hard: 1 week (if geometric-mean API is thin)

## References

### Papers
- Hardy, Littlewood, Polya, Inequalities (1934), Ch. II — power means monotonicity.

### Online Resources
- https://en.wikipedia.org/wiki/Generalized_mean — the monotonicity theorem and sign-crossing case.

### Mathlib
- `Mathlib.Analysis.MeanInequalities` — weighted AM–GM.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.rpow` monotonicity.

## Metadata

```yaml
tags:
  - analysis
  - inequalities
  - power-means
  - mean-inequalities
  - duality
related_proofs:
  - jensen-inequality
  - cauchy-schwarz-integral
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 5/10
**Tractability**: 7/10
