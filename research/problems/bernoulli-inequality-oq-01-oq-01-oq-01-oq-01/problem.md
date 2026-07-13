# Problem: Sharp left endpoint a_n* of the strict Bernoulli inequality (odd n) — uniqueness and −2 asymptotic

**Slug**: bernoulli-inequality-oq-01-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For odd `n ≥ 3`, let
$$
g_n(t) \;=\; \frac{t^n - n\,t + (n-1)}{(t-1)^2}.
$$
Then `g_n` has a unique real root `a_n^* < -1`, it is the left endpoint of the interval on which the strict Bernoulli inequality `(1+x)^n > 1 + n x` holds for `x = t-1`, and
$$
a_n^* \;=\; -2 - \Theta(1/n) \qquad (n \to \infty, \ n \text{ odd}).
$$

### Plain Language

The parent fixes the *sharp left endpoint* `a_n^*` of the region where the strict Bernoulli inequality holds for odd exponents. This leaf asks two concrete things: (1) show that on `(-∞, -1)` the relevant polynomial factor has exactly one root, so `a_n^*` is well defined as that unique root; and (2) prove the sharp asymptotic that this endpoint sits just below `-2`, approaching `-2` at rate `Θ(1/n)` as the odd exponent grows.

### Why This Matters

It upgrades the parent's existence/sharpness statement to a *quantitative* description of the endpoint: a uniqueness characterization (so `a_n^*` is canonical) plus a closed asymptotic. This is the kind of explicit constant tracking that turns a qualitative sharpness result into a usable bound, and it exercises root-counting/monotonicity machinery on a parametric polynomial.

## Known Results

### What's Already Proven

- Parent `bernoulli-inequality-oq-01-oq-01-oq-01`: existence of the sharp left endpoint of the strict Bernoulli inequality for odd `n`.
- Mathlib: `Polynomial`, `Polynomial.roots`, strict mono via `StrictMonoOn`, `intermediate_value_Ioo`, `Polynomial.derivative`, `Filter.Tendsto`, `Asymptotics.IsBigO`/`IsLittleO`.

### What's Still Open

- Uniqueness of the root of the numerator factor on `(-∞,-1)`.
- The `a_n^* = -2 - Θ(1/n)` asymptotic with explicit constants in the `Θ`.

### Our Goal

Prove `∃! t < -1, t^n - n t + (n-1) = 0` (numerator factor, after removing the `(t-1)^2` denominator), identify it with `a_n^*`, and establish `Tendsto (fun n => a_n^*) atTop (𝓝 (-2))` together with the two-sided `Θ(1/n)` rate.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `bernoulli-inequality-oq-01-oq-01-oq-01` | parent: sharp left endpoint exists | polynomial sign analysis, strict inequality |
| `bernoulli-inequality` | base Bernoulli inequality | induction, convexity |

## Initial Thoughts

### Potential Approaches

1. **Monotonicity + IVT for uniqueness**: show the numerator `h_n(t) = t^n - n t + (n-1)` is strictly monotone on `(-∞,-1)` for odd `n` (sign of `h_n' = n t^{n-1} - n = n(t^{n-1}-1)`, with `t^{n-1} > 1` for `t < -1` since `n-1` is even), giving a unique sign change.
   - Why it might work: `h_n'` is sign-definite on the ray, so `h_n` is strictly monotone ⇒ at most one root; IVT gives at least one.
   - Risk: bookkeeping the parity of `n-1` (even) inside Lean's `Polynomial`/real-power lemmas.

2. **Asymptotics by substitution `t = -2 + s/n`**: expand `h_n(-2 + s/n)` and extract the leading balance to pin the `Θ(1/n)` correction.
   - Why it might work: `(-2)^n` dominates; the linear term `-n t` contributes the `+2n` that balances; matching orders yields the rate.
   - Risk: controlling the remainder of the expansion rigorously (needs a clean `IsBigO` bound).

### Key Difficulties

- Clean handling of odd/even parity for `t^{n}` and `t^{n-1}` at negative `t`.
- Making the `Θ(1/n)` two-sided bound rigorous rather than heuristic.

### What Would a Proof Need?

- Key lemma 1: `StrictMonoOn h_n (Iio (-1))` for odd `n`.
- Key lemma 2: sign change `h_n(-2) < 0 < h_n(-1^-)` (or appropriate endpoints) to locate the root near `-2`.
- Key lemma 3: substitution estimate giving `a_n^* + 2 = Θ(1/n)`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Uniqueness via monotonicity + IVT is standard and well supported in Mathlib.
- Parent is verified, 0-axiom; the polynomial setup is reusable.
- The sharp two-sided asymptotic is the harder half; a one-sided `Tendsto (… ) (𝓝 (-2))` is a safe milestone.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days (uniqueness + convergence to −2)
- If hard: the explicit two-sided `Θ(1/n)` constants

## References

### Papers
- D. S. Mitrinović, *Analytic Inequalities* — sharp forms of Bernoulli's inequality.

### Online Resources
- Standard references on Bernoulli's inequality endpoints and root asymptotics.

### Mathlib
- `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`, `Mathlib/Analysis/Calculus/MeanValue.lean` — monotonicity from derivative sign.
- `Mathlib/Topology/Algebra/Order/IntermediateValue.lean` — IVT.

## Metadata

```yaml
tags:
  - analysis
  - inequality
  - bernoulli-inequality
  - sharp-constant
  - asymptotics
related_proofs:
  - bernoulli-inequality-oq-01-oq-01-oq-01
  - bernoulli-inequality
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
