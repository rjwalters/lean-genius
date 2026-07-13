# Problem: L'Hôpital's Rule — Relationship to Taylor Series

**Slug**: lhopital-oq-04
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap (L'Hôpital's Rule OQ-04)

## Problem Statement

### Formal Statement

For analytic functions $f, g$ with $f(a) = g(a) = 0$ and $g'(a) \neq 0$, L'Hôpital's rule gives:

$$\lim_{x \to a} \frac{f(x)}{g(x)} = \frac{f'(a)}{g'(a)}$$

The Taylor series perspective explains this: near $x = a$:
$$f(x) = f'(a)(x-a) + \frac{f''(a)}{2!}(x-a)^2 + \cdots$$
$$g(x) = g'(a)(x-a) + \frac{g''(a)}{2!}(x-a)^2 + \cdots$$

So $f(x)/g(x) \to f'(a)/g'(a)$ because the leading-order terms dominate.

**Goal**: Formalize this connection in Lean 4 — either:
1. Prove L'Hôpital's rule *via* Taylor expansion (as an alternative to the standard MVT proof), OR
2. Prove that repeated application of L'Hôpital on $f/g$ (when higher derivatives also vanish) is equivalent to comparing Taylor coefficients.

### Plain Language

L'Hôpital's rule and Taylor series are two sides of the same coin for $0/0$ indeterminate forms. The standard Lean proof of L'Hôpital uses the Mean Value Theorem. But there's a cleaner story: if both $f$ and $g$ vanish at $a$, then near $a$ they behave like their derivatives, because their Taylor expansions start at the linear term. This insight can be made precise and formalized.

### Why This Matters

1. **Pedagogical value**: The Taylor series derivation of L'Hôpital is more illuminating than the MVT proof
2. **Mathlib gap**: Mathlib has `HasDerivAt.lhopital_zero_right` but may lack the Taylor series connection
3. **Generalization**: Iterated L'Hôpital (when $f^{(k)}(a) = g^{(k)}(a) = 0$ for $k < n$) is exactly comparing $n$th Taylor coefficients — formalizing this cleanly would be a useful Mathlib lemma

## Known Results

### What's Already Proven

- `lhopital` (gallery): L'Hôpital's rule for $0/0$ via MVT — verified
- `HasDerivAt.lhopital_zero_right` (Mathlib): L'Hôpital for one-sided limits
- `taylorWithRemainder` (Mathlib): Taylor's theorem with Lagrange remainder

### What's Still Open

- Formalization of the Taylor series *derivation* of L'Hôpital (alternative proof)
- The iterated case: $k$-fold L'Hôpital = $k$th Taylor coefficient ratio
- Clean Lean statement connecting `HasDerivAt` with Taylor expansion coefficients

### Our Goal

Formalize the precise statement: for $f, g \in C^\infty(a)$ with $f(a) = g(a) = 0$, the limit $\lim_{x \to a} f(x)/g(x) = f'(a)/g'(a)$ follows directly from Taylor's theorem applied to $f$ and $g$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `lhopital` | Parent proof (MVT-based) | `HasDerivAt`, Mean Value Theorem |
| `basel-problem` | Uses Taylor series machinery | `Real.sin`, `Real.cos` Taylor expansion |
| `binomial-theorem` | Polynomial expansion techniques | `Finset.sum`, ring operations |

## Initial Thoughts

### Potential Approaches

1. **Direct Taylor derivation**: Use Mathlib's `taylorWithRemainder` to write $f(x) = f'(a)(x-a) + O((x-a)^2)$ and $g(x) = g'(a)(x-a) + O((x-a)^2)$, then divide and take the limit.
   - Why it might work: All components are in Mathlib — `taylorWithRemainder`, limit theorems, continuity
   - Risk: Division of asymptotic expansions in Lean requires care; need to handle the case $g'(a) \neq 0$

2. **Iterated case formalization**: Prove that if $f^{(k)}(a) = 0$ for $k = 0, \ldots, n-1$ and $g^{(n)}(a) \neq 0$, then $\lim_{x \to a} f/g = f^{(n)}(a)/g^{(n)}(a)$.
   - Why it might work: Induction on the vanishing order, using L'Hôpital at each step
   - Risk: Requires n-fold differentiability and careful index management

3. **Coefficient comparison lemma**: Prove `taylorCoeff_ratio`: if $f(a) = 0$ and $g(a) = 0$, then $f(x)/g(x) \to \text{taylorCoeff}(f, a, 1) / \text{taylorCoeff}(g, a, 1)$.
   - Why it might work: Clean abstract statement connecting two existing Mathlib APIs
   - Risk: `taylorCoeff` notation in Mathlib may need adaptation

### Key Difficulties

- Lean's `Filter.Tendsto` limit framework vs pointwise limits needs alignment
- Division in a limit: need to show $g'(a) \neq 0$ prevents denominator collapse
- `taylorWithRemainder` gives error term; need to show error is $o(x-a)$ in the limit

### What Would a Proof Need?

- `Real.differentiableAt_taylorWithRemainder` or similar
- `Filter.Tendsto.div_const` — limit of quotient
- `HasDerivAt` for both $f$ and $g$ at $a$
- `isLittleO` framework for the error bound

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- L'Hôpital and Taylor series are both mature Mathlib topics
- `taylorWithRemainder` and `HasDerivAt` are accessible APIs
- The connection is mathematically straightforward (asymptotic dominance)
- The main challenge is Lean bookkeeping for the error terms

## References

### Papers
- Rudin, W. *Principles of Mathematical Analysis*, 3rd ed., Chapter 5 — L'Hôpital and Taylor

### Mathlib
- `Analysis.Calculus.MeanValue` — Mean Value Theorem (used by existing L'Hôpital)
- `Analysis.Calculus.Taylor` — Taylor's theorem with remainder
- `Mathlib.Analysis.Calculus.LHopital` — Existing L'Hôpital formalization
- `Filter.isLittleO` — Asymptotic notation

## Metadata

```yaml
tags:
  - analysis
  - calculus
  - lhopital
  - taylor-series
  - formalization
  - mathlib
related_proofs:
  - lhopital
  - basel-problem
difficulty: medium
source: gallery-gap
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 7/10
