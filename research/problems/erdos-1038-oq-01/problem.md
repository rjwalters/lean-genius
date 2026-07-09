# Problem: Exact Value of the Infimum Sublevel-Set Measure (Erdős #1038)

**Slug**: erdos-1038-oq-01
**Created**: 2026-07-09T00:00:00Z
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\inf_{f} \left| \{ x \in \mathbb{R} : |f(x)| < 1 \} \right| \;=\; ?, \qquad f(x) = \prod_{i=1}^{n} (x - r_i),\; r_i \in [-1,1],\; n \ge 1,
$$

where $|\cdot|$ denotes Lebesgue measure and the infimum ranges over all non-constant monic polynomials whose roots all lie in $[-1,1]$. The current best bounds are $2^{4/3} - 1 \approx 1.519 \le \inf_f |\{x : |f(x)| < 1\}| \le 1.835$; the exact value is unknown.

### Plain Language

Take a monic polynomial whose roots all sit inside the interval $[-1,1]$, and look at the set of real numbers where the polynomial has absolute value less than $1$. That "sublevel set" always has some total length. Erdős, Herzog, and Piranian asked how large and how small this length can be as the polynomial varies. Tao settled the largest possible length in 2025 (it is $2\sqrt{2}$), but the smallest possible length — the infimum — is still not pinned down. We know it lies somewhere between about $1.519$ and $1.835$, and the goal is to determine its exact value.

### Why This Matters

Determining the infimum would complete the metric picture of polynomial sublevel sets begun by Erdős–Herzog–Piranian (1958) and continued by Tao (2025). The quantity links polynomial approximation on $[-1,1]$ to logarithmic potential theory, equilibrium measures, and transfinite diameter, so an exact answer would sharpen our understanding of how root placement constrains the region where a monic polynomial stays small. It also feeds into the sibling Erdős problems (#1039–#1046) on lemniscate geometry and disc containment, where the same sublevel sets are studied topologically and geometrically.

## Known Results

### What's Already Proven

- Supremum equals $2\sqrt{2}$ for monic polynomials with all roots in $[-1,1]$ — Tao (2025), announced December 2025.
- Upper bound $\sup \le 2\sqrt{2}$ for roots in $\{-1,1\}$, plus $\inf < 2$ via families like $(x+1)(x-1)^3$ — Erdős, Herzog, Piranian (1958).
- Lower bound $\inf \ge 2^{4/3} - 1 \approx 1.519$ from potential-theoretic estimates — see the erdos-1038 gallery entry.

### What's Still Open

- The exact value of $\inf_f |\{x : |f(x)| < 1\}|$ within the interval $[1.519, 1.835]$.
- Whether that infimum is attained by an explicit polynomial or realized only as a limit of a polynomial family.

### Our Goal

Determine (or tightly bound) the exact value of the infimum, and formalize the resulting statement in Lean 4 by improving the current explicit lower and upper bound witnesses. As a first tractable step we target narrowing the gap: sharpen either the lower bound beyond $2^{4/3} - 1$ or the upper bound below $1.835$ using an explicit polynomial family, and formalize the measure estimate for that witness.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1038 | Parent entry stating both the supremum ($2\sqrt{2}$) and the open infimum bounds | Measure theory, potential theory, polynomial analysis |
| erdos-1040 | Generalizes sublevel-set measure to closed sets $F \subseteq \mathbb{C}$ via transfinite diameter | Transfinite diameter, logarithmic capacity |
| erdos-1046 | Disc containment for connected lemniscates $\{z : |f(z)| < 1\}$ | Lemniscate geometry, conformal estimates |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Extremal polynomial families. Study families such as $(x+1)^a (x-1)^b$ and Chebyshev-type combinations, compute the measure of $\{x : |f(x)| < 1\}$ explicitly, and minimize over the family to push the upper bound below $1.835$.
   - Why it might work: the current bounds already come from explicit families, so a richer parametrization may reveal a sharper minimizer.
   - Risk: the true minimizer may be a limit object, so no finite family attains the infimum and only asymptotic estimates result.

2. **Approach B**: Potential-theoretic lower bound. Represent the sublevel-set measure via the logarithmic potential / equilibrium measure of the root distribution and apply capacity inequalities to raise the lower bound above $2^{4/3} - 1$.
   - Why it might work: Tao's supremum proof shows potential theory captures the extremal behavior; the same machinery should constrain the minimum.
   - Risk: the required capacity estimates are not in Mathlib, so formalization would need substantial new infrastructure.

### Key Difficulties

- The infimum may be an irrational constant with no closed form, making an exact Lean statement hard to phrase.
- Lebesgue measure of a semialgebraic sublevel set requires careful ENNReal handling and Mathlib currently lacks logarithmic capacity / equilibrium measure theory.

### What Would a Proof Need?

- Key lemma 1: an explicit formula (or sharp bound) for $|\{x : |f(x)| < 1\}|$ for a chosen parametric family.
- Key lemma 2: a potential-theoretic lower bound tying the measure to the logarithmic capacity of the root set $[-1,1]$.
- Technical requirements: `MeasureTheory.volume` reasoning over `ENNReal`, monic-polynomial factorization in Mathlib, and real-analytic estimates for the sublevel set boundary.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The exact infimum is an open research problem with a substantial $[1.519, 1.835]$ gap and no known closed form.
- Related metric-property questions (e.g. Tao's supremum) required serious potential theory, indicating the infimum is comparably hard.
- Mathlib provides Lebesgue measure and polynomial factorization but no equilibrium-measure or transfinite-diameter theory, so a full formalization would need new groundwork.

**Estimated Effort**:
- Exploration: several days
- If tractable (narrowing the gap with an explicit witness): weeks
- If hard (exact value): unknown / open-ended

## References

### Papers
- P. Erdős, G. Herzog, G. Piranian, "Metric properties of polynomials", J. d'Analyse Math. 6 (1958), 125–148 — original source posing the infimum question.
- T. Tao, "Sublevel set measure for monic polynomials", arXiv (2025) — resolved the supremum at $2\sqrt{2}$.
- T. Ransford, "Potential Theory in the Complex Plane", Cambridge Univ. Press (1995) — logarithmic capacity and transfinite diameter background.

### Online Resources
- https://erdosproblems.com/1038 — canonical statement and status of Erdős Problem #1038.

### Mathlib
- Mathlib.MeasureTheory.Measure.Lebesgue.Basic — Lebesgue measure `volume` on $\mathbb{R}$ used for the sublevel-set length.
- Mathlib.Algebra.Polynomial.Monic — monic polynomial definitions and factorization needed to model the root constraint.

## Metadata

```yaml
tags:
  - erdos
  - measure-theory
  - polynomials
  - potential-theory
  - real-analysis
related_proofs:
  - erdos-1038
  - erdos-1040
difficulty: high
source: proof-suggestion
created: 2026-07-09T00:00:00Z
```
