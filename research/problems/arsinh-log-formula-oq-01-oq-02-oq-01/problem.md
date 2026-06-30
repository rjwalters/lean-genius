# Problem: arcosh Antiderivative ∫ 1/√(t²−1) dt = arcosh t + C

**Slug**: arsinh-log-formula-oq-01-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\frac{d}{dt}\operatorname{arcosh} t = \frac{1}{\sqrt{t^2-1}} \quad (t > 1),
\qquad
\int \frac{1}{\sqrt{t^2-1}}\,dt = \operatorname{arcosh} t + C \quad (t > 1).
$$

Equivalently, for `1 < a ≤ b`,
$$
\int_a^b \frac{1}{\sqrt{t^2-1}}\,dt = \operatorname{arcosh} b - \operatorname{arcosh} a
= \log\!\left(b + \sqrt{b^2-1}\right) - \log\!\left(a + \sqrt{a^2-1}\right).
$$

### Plain Language

The parent entry established the logarithmic form of `arcosh` and its addition law.
A sibling open question proved the `arsinh` antiderivative `∫ 1/√(1+t²) dt = arsinh t + C`.
This problem proves the cosh-side counterpart: that `1/√(t²−1)` integrates to `arcosh t`
on the domain `t > 1`, both as a `HasDerivAt`/`deriv` statement and as a definite-integral
(FTC) statement, and ties it back to the logarithmic closed form.

### Why This Matters

It completes the symmetric pair of inverse-hyperbolic antiderivatives anchored by the
arsinh-log-formula entry, giving a self-contained, axiom-free Lean account of the standard
table integral `∫ dt/√(t²−1)`. It also exercises Mathlib's `Real.arcosh` derivative API on a
restricted domain (`t > 1`), where the radicand is positive.

## Known Results

### What's Already Proven

- `arsinh-log-formula-oq-01-oq-02` — the arcosh logarithmic form `arcosh t = log(t + √(t²−1))` and its addition law (verified, 0-axiom).
- Sibling open question — the arsinh antiderivative `∫ 1/√(1+t²) dt = arsinh t + C` (the model to mirror).
- Mathlib: `Real.arcosh`, `Real.cosh_arcosh`, `Real.arcosh_le_arcosh`, monotonicity, and derivative lemmas for `Real.sqrt` and `Real.log`.

### What's Still Open

- A clean `HasDerivAt Real.arcosh (1/√(t²−1)) t` for `t > 1` in this repository's gallery.
- The corresponding definite-integral / FTC packaging over `[a,b] ⊂ (1,∞)`.

### Our Goal

Prove the derivative identity for `t > 1`, then derive the indefinite and definite integral
forms via `intervalIntegral.integral_deriv_eq_sub` (FTC-2), and connect to the logarithmic
closed form already in the parent.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| arsinh-log-formula-oq-01-oq-02 | Parent: arcosh log form + addition law | inverse-hyperbolic identities |
| arsinh-log-formula-oq-01 | Grandparent: arsinh logarithmic form | log/sqrt manipulation |

## Initial Thoughts

### Potential Approaches

1. **Approach A — differentiate the closed form**: Use `arcosh t = log(t + √(t²−1))`,
   apply chain rule (`Real.hasDerivAt_log`, `Real.hasDerivAt_sqrt`) for `t > 1`, and simplify
   `1 + t/√(t²−1) = (√(t²−1)+t)/√(t²−1)` so the `(t+√(t²−1))` factor cancels, leaving `1/√(t²−1)`.
   - Why it might work: avoids needing a dedicated Mathlib `hasDerivAt_arcosh` lemma.
   - Risk: algebra to cancel the composite factor; need `t²−1 > 0` everywhere.

2. **Approach B — use Mathlib's arcosh derivative if available**: If `Real.hasDerivAt_arcosh`
   exists, apply directly; otherwise fall back to Approach A.
   - Why it might work: shortest path.
   - Risk: lemma may not exist or may have different hypotheses.

### Key Difficulties

- Restricting to `t > 1` so `√(t²−1)` is positive and differentiable (its argument is nonzero).
- Cancelling the `(t + √(t²−1))` factor cleanly in the chain-rule output.

### What Would a Proof Need?

- Key lemma 1: `HasDerivAt (fun t => Real.sqrt (t^2 - 1)) (t/√(t²−1)) t` for `t > 1`.
- Key lemma 2: chain rule through `Real.log` with positive argument `t + √(t²−1) > 0`.
- Technical requirements: `Real.sqrt_pos`, `Real.sq_sqrt`, field_simp/ring to finish.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The arsinh sibling was completed by the same template, so the route is proven.
- Mathlib has all derivative primitives for `log`, `sqrt`, and powers.
- The only new wrinkle is the `t²−1` radicand and the `t > 1` domain restriction.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days
- If hard: unlikely to exceed a few days

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` / hyperbolic inverse files — `Real.arcosh` and identities.
- `Mathlib.Analysis.Calculus.FTC` — `intervalIntegral.integral_deriv_eq_sub` for the definite-integral form.

## Metadata

```yaml
tags:
  - analysis
  - calculus
  - hyperbolic-functions
related_proofs:
  - arsinh-log-formula-oq-01-oq-02
  - arsinh-log-formula-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
