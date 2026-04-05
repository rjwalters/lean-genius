# Problem: Sharper Birthday Bound via Higher-Order Taylor Expansion

**Slug**: birthday-problem-oq-02-oq-01-oq-01
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\prod_{i=0}^{k-1}\left(1 - \frac{i}{d}\right) \ge \exp\!\left(-\frac{k(k-1)}{2d} - \frac{k^2(k-1)^2}{4d^2}\right)
$$

for $0 \le k \le d$, using the second-order Taylor remainder of $\ln(1-x)$.

### Plain Language

The parent proof `birthday-problem-oq-02` formalizes the upper bound for collision probability in the birthday problem. This problem asks: can the matching **lower bound** be formalized in Lean 4?

The lower bound requires the second-order term of $\ln(1-x) \approx -x - x^2/2 - \ldots$, giving a sharper two-sided bound on the birthday collision threshold.

### Why This Matters

1. **Completes the birthday problem formalization** — the upper bound alone is a one-sided estimate; adding the lower bound gives the tight asymptotic $n \approx \sqrt{2d \ln 2}$.
2. **Taylor remainder technique** — formalizing the two-sided Taylor estimate for $\ln(1-x)$ is reusable across probability and analysis proofs.
3. **Mathlib contribution opportunity** — a clean lemma for second-order logarithm bounds could go upstream.

## Known Results

### What's Already Proven

- Upper bound: $\prod(1-i/d) \le \exp(-k(k-1)/(2d))$ — proved in `birthday-problem-oq-02`
- First-order Taylor: $\ln(1-x) \ge -x/(1-x)$ (or similar) available via `Real.add_one_le_exp`

### What's Still Open

- Formalize the lower bound using the second-order Taylor remainder $\ln(1-x) \ge -x - x^2/2$ for $x \in [0,1)$
- Prove the product bound from this remainder estimate
- (Stretch) Poisson approximation as $d \to \infty$ with $k^2/d \to \lambda$

### Our Goal

Formalize the lower bound inequality above, specifically:
- Second-order Taylor lower bound for $\ln(1-x)$: $\ln(1-x) \ge -x - x^2/2$ for $x \in [0,1)$
- Sum the bound over $i = 0,\ldots,k-1$: $\sum -i/d - (i/d)^2/2 \ge -k(k-1)/(2d) - k^2(k-1)^2/(4d^2)$
- Exponentiate to get the product lower bound

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `birthday-problem-oq-02` | Parent proof: upper bound | Taylor, Finset.prod |
| `birthday-problem` | Base birthday problem | Combinatorics, probability |
| `amgm-inequality` | Related Taylor-based inequalities | nlinarith, Taylor |

## Initial Thoughts

### Potential Approaches

1. **Via `Real.log_le_sub_one_of_le`**: Use Mathlib's log bounds directly
   - Why it might work: Mathlib has `Real.add_one_le_exp` and related lemmas
   - Risk: The second-order bound may not be in Mathlib and need manual proof

2. **Direct Taylor remainder**: Prove $\ln(1-x) \ge -x - x^2/2$ via derivative argument
   - Why it might work: Can use convexity of $-\ln(1-x)$ and its second derivative
   - Risk: Requires interval calculus machinery

3. **nlinarith/polyrith approach**: Try automated tactics on the expanded inequality
   - Why it might work: After taking exp and linearizing, may be polynomial
   - Risk: Product form is not polynomial; needs `Finset.prod` manipulation

### Key Difficulties

- Converting the product lower bound to a sum bound (via log monotonicity)
- Formalizing the second-order Taylor lower bound for log (not just first-order)
- Summing the quadratic terms $\sum (i/d)^2$

### What Would a Proof Need?

- Key lemma 1: `log_one_sub_ge` — $\ln(1-x) \ge -x - x^2/2$ for $x \in [0,1)$
- Key lemma 2: `sum_div_sq_bound` — $\sum_{i=0}^{k-1} (i/d)^2 \le k^2(k-1)^2/(4d^2) \cdot 2$
- Mathlib: `Real.log_le_sub_one_of_le`, `Real.exp_le_one_add_of_nonpos`, `Finset.sum_range_succ`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Parent proof `birthday-problem-oq-02` is already verified, providing the framework
- Second-order Taylor bounds are classical — likely formalizable with `nlinarith` + `norm_num`
- Sum of squares formula $\sum i^2 = k(k-1)(2k-1)/6$ is in Mathlib (`Finset.sum_range_succ`)

**Estimated Effort**:
- Exploration: 1-2 OODA cycles
- If tractable: Single PR with 1-2 key lemmas

## References

### Papers
- Diaconis & Mosteller (1989). "Methods for Studying Coincidences." JASA 84(408):853–861.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — Real.log bounds
- `Mathlib.Algebra.BigOperators.Order` — Finset.prod monotonicity
- `Mathlib.Topology.Algebra.Order.LiminfLimsup` — asymptotics

## Metadata

```yaml
tags:
  - probability
  - combinatorics
  - asymptotics
  - taylor-expansion
  - birthday-problem
related_proofs:
  - birthday-problem
  - birthday-problem-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-05
tier: B
significance: 5
tractability: 7
```
