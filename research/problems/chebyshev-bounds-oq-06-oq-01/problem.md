# Problem: Sharpen central binomial upper bound to 4^n/√(πn) via Stirling

**Slug**: chebyshev-bounds-oq-06-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\binom{2n}{n} \le \frac{4^n}{\sqrt{\pi n}} \quad (n \ge 1), \qquad\text{and}\qquad \binom{2n}{n} \sim \frac{4^n}{\sqrt{\pi n}} \ (n \to \infty).
$$

### Plain Language

The parent proof (`chebyshev-bounds-oq-06`) gives the elementary two-sided bound $\frac{4^n}{2n+1} \le \binom{2n}{n} \le 4^n$. This open question asks to sharpen the **upper** bound to the Stirling-quality constant $\frac{4^n}{\sqrt{\pi n}}$, and to establish the matching asymptotic $\binom{2n}{n} \sim \frac{4^n}{\sqrt{\pi n}}$, using Stirling's approximation as available in Mathlib.

### Why This Matters

- The constant $\frac{4^n}{\sqrt{\pi n}}$ is the *sharp* leading-order size of the central binomial coefficient; it is the workhorse estimate behind Chebyshev-type prime-counting bounds, random-walk return probabilities, and Catalan-number asymptotics.
- Upgrading the gallery's crude $\le 4^n$ to the sharp asymptotic connects the entry to Mathlib's Stirling infrastructure and unblocks downstream analytic-number-theory refinements.

## Known Results

### What's Already Proven

- `chebyshev-bounds-oq-06` — two-sided bound $\frac{4^n}{2n+1} \le \binom{2n}{n} \le 4^n$ (parent, verified, 0-axiom).
- Mathlib `Stirling.factorial_isEquivalent_stirling` / `Nat.factorial` asymptotics — `n! ∼ √(2πn)(n/e)^n`.
- `Mathlib.Analysis.SpecialFunctions.Stirling` provides the central binomial asymptotic scaffolding (`Stirling.centralBinom_isEquivalent`-style results in recent Mathlib).

### What's Still Open

- Whether Mathlib's Stirling API exposes the exact `IsEquivalent` statement for `centralBinom`, or whether it must be derived from `factorial_isEquivalent_stirling` by ratio.
- A clean, non-asymptotic upper bound $\binom{2n}{n} \le 4^n/\sqrt{\pi n}$ valid for all $n \ge 1$ (the asymptotic alone does not give a uniform inequality).

### Our Goal

1. Prove the asymptotic $\binom{2n}{n} \sim \frac{4^n}{\sqrt{\pi n}}$ via `Filter.Tendsto`/`Asymptotics.IsEquivalent`, ideally reusing Mathlib's Stirling equivalence.
2. If tractable, prove the uniform upper bound $\binom{2n}{n} \le 4^n/\sqrt{\pi n}$ (requires a monotone/error-term argument on the Stirling ratio, e.g. via the Wallis product or a log-convexity estimate).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chebyshev-bounds-oq-06 | Parent; supplies the coarse bound being sharpened | `Nat.choose`, induction, `4^n` bounds |
| basel-problem-oq-06 | Uses Mathlib special-function asymptotics (`HasSum`, ζ-values) in the gallery | `HasSum`, special functions |

## Initial Thoughts

### Potential Approaches

1. **Reuse Mathlib Stirling equivalence (recommended)**: locate the central binomial / factorial `IsEquivalent` lemma in `Mathlib.Analysis.SpecialFunctions.Stirling`, then compute $\binom{2n}{n} = (2n)!/(n!)^2$ and take the ratio of equivalences.
   - Why it might work: Mathlib already contains the hard analytic content (the Wallis-product limit $\sqrt\pi$); the deliverable becomes algebraic bookkeeping of `IsEquivalent`.
   - Risk: `IsEquivalent` ratio/product lemmas require nonvanishing hypotheses and careful rewriting of `(n/e)^n` factors.

2. **Direct Wallis-product route**: derive $\binom{2n}{n}/4^n \sim 1/\sqrt{\pi n}$ from `Real.Gamma` / Wallis identities.
   - Why it might work: self-contained.
   - Risk: reproves content Mathlib may already have; more work.

### Key Difficulties

- The uniform (all-$n$) inequality is strictly harder than the asymptotic and needs an explicit error bound on the Stirling ratio.
- Matching Mathlib's exact naming/shape for the Stirling equivalence to avoid re-deriving $\sqrt\pi$.

### What Would a Proof Need?

- Key lemma 1: `Stirling`-based `IsEquivalent` for `n!` (present in Mathlib).
- Key lemma 2: `centralBinom n = (2n)! / (n!)^2` cast to `ℝ` and its `IsEquivalent` to `4^n/√(πn)`.
- Key lemma 3 (stretch): monotonicity of $\binom{2n}{n}\sqrt{\pi n}/4^n \uparrow 1$ for the uniform upper bound.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- If Mathlib exposes the central-binomial Stirling equivalence, the asymptotic half is a short reduction.
- The uniform inequality half is the risk; it may be deferred as a stretch goal.
- Prior gallery work (`basel-problem-oq-06`) shows special-function asymptotics are usable in this codebase.

**Estimated Effort**:
- Exploration: hours (locate the right Mathlib Stirling lemma)
- If tractable (asymptotic only): 1–3 days
- If hard (uniform inequality): unknown

## References

### Papers
- Robbins, "A Remark on Stirling's Formula", *Amer. Math. Monthly* 62 (1955) — sharp two-sided Stirling error bounds usable for the uniform inequality.

### Online Resources
- OEIS A000984 (central binomial coefficients).

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Stirling` — Stirling equivalence, Wallis product limit.
- `Mathlib.Analysis.Asymptotics.Asymptotics` — `IsEquivalent`, ratio/product lemmas.
- `Mathlib.Combinatorics.Choose.Central` — `Nat.centralBinom`, `centralBinom` bounds.

## Metadata

```yaml
tags:
  - analytic-number-theory
  - stirling
  - binomial-coefficients
  - asymptotics
related_proofs:
  - chebyshev-bounds-oq-06
  - basel-problem-oq-06
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
