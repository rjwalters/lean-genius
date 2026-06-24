# Problem: Improper integral ∫₁ᵇ 1/√(t²−1) dt = arcosh b

**Slug**: arsinh-log-formula-oq-01-oq-02-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\int_{1}^{b} \frac{1}{\sqrt{t^2 - 1}}\,dt \;=\; \operatorname{arcosh} b \;=\; \log\!\left(b + \sqrt{b^2 - 1}\right), \qquad b \ge 1,
$$

obtained as the limit $\displaystyle \lim_{a \to 1^{+}} \int_{a}^{b} \frac{1}{\sqrt{t^2-1}}\,dt$ across the integrable singularity at $t = 1$.

### Plain Language

The parent entry proves the **antiderivative** identity $\int 1/\sqrt{t^2-1}\,dt = \operatorname{arcosh} t + C$ on the open interval $(1, \infty)$. This leaf upgrades that to a genuine **definite (improper) integral** from $1$ to $b$: the integrand blows up at the lower endpoint $t = 1$, so the integral is improper, but it converges because $1/\sqrt{t^2-1} \sim 1/\sqrt{2(t-1)}$ is integrable there. The value is exactly $\operatorname{arcosh} b$.

### Why This Matters

Closes the loop from antiderivative to evaluated definite integral, exercising Mathlib's improper-integral / `intervalIntegral` limit machinery across a singular endpoint — a reusable pattern for the whole family of inverse-hyperbolic / inverse-trig integrals.

## Known Results

### What's Already Proven

- Parent `arsinh-log-formula-oq-01-oq-02-oq-01` — the arcosh antiderivative $\int 1/\sqrt{t^2-1}\,dt = \operatorname{arcosh} t + C$ on $(1,\infty)$.
- Mathlib: `Real.arcosh`, derivative lemmas for `arcosh`, `intervalIntegral.integral_eq_sub_of_hasDerivAt`, and continuity/limit lemmas (`Filter.Tendsto`, `intervalIntegral` continuity in endpoints).

### What's Still Open

- The evaluated improper integral as a single named theorem.
- Establishing convergence at the singular endpoint $t = 1^{+}$ rather than only on compact subintervals $[a,b] \subset (1,\infty)$.

### Our Goal

Prove the displayed equality as a clean, axiom-free Lean theorem, deriving it from the parent antiderivative by a continuity/limit argument as $a \to 1^{+}$ (using $\operatorname{arcosh} 1 = 0$).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| arsinh-log-formula-oq-01-oq-02-oq-01 | Parent: arcosh antiderivative | FTC, derivative of arcosh |
| arsinh-log-formula-oq-01-oq-01 | Sibling: arsinh = log formula | log/hyperbolic identities |

## Initial Thoughts

### Potential Approaches

1. **Approach A — FTC on $[a,b]$ then take $a\to1^{+}$**: Apply the parent antiderivative on $[a,b]$ to get $\int_a^b = \operatorname{arcosh} b - \operatorname{arcosh} a$, then pass to the limit using continuity of `arcosh` at $1$ and $\operatorname{arcosh} 1 = 0$.
   - Why it might work: avoids re-deriving anything; the singularity is handled purely by the endpoint limit.
   - Risk: packaging the improper integral as a `Tendsto` of `intervalIntegral` (Mathlib has `intervalIntegral` but the improper limit must be assembled by hand).

2. **Approach B — explicit `arcosh = log(b+√(b²−1))` form**: Prove the log form directly and differentiate to match the integrand.
   - Why it might work: keeps everything in elementary `Real.log`/`sqrt`.
   - Risk: more algebra; derivative bookkeeping of the log expression.

### Key Difficulties

- Expressing the improper integral and its convergence in Mathlib idiom.
- Continuity / value of `arcosh` at the boundary point $1$.

### What Would a Proof Need?

- Key lemma 1: the parent FTC identity on compact $[a,b] \subset (1,\infty)$.
- Key lemma 2: $\operatorname{arcosh}$ continuous at $1$ with $\operatorname{arcosh} 1 = 0$.
- Technical requirements: a `Tendsto` statement gluing the compact-interval integrals to the improper value.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The hard analytic content (the antiderivative) is already proven in the parent.
- Mathlib has the FTC and the limit/continuity tools; the work is assembling the improper-integral limit.
- Similar inverse-hyperbolic integral evaluations have been formalized in the gallery family.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 1–2 days
- If hard: unknown (if the improper-integral packaging proves fiddly)

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` / hyperbolic analogues — `Real.arcosh` and derivatives.
- `Mathlib.MeasureTheory.Integral.FundThmCalculus` — FTC for `intervalIntegral`.

## Metadata

```yaml
tags:
  - analysis
  - calculus
  - improper-integral
  - arcosh
  - hyperbolic-functions
related_proofs:
  - arsinh-log-formula-oq-01-oq-02-oq-01
  - arsinh-log-formula-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
