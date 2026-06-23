# Problem: Optimal Convergence Rate for Arctangent-Based Pi Series

**Slug**: leibniz-pi
**Created**: 2026-03-11
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Leibniz: } \left|\frac{\pi}{4} - \sum_{k=0}^{n} \frac{(-1)^k}{2k+1}\right| = \Theta\left(\frac{1}{n}\right)
$$

$$
\text{Machin: } \frac{\pi}{4} = 4\arctan\frac{1}{5} - \arctan\frac{1}{239}, \quad \text{error} = O(5^{-n})
$$

### Plain Language

The Leibniz series for pi converges very slowly — O(1/n). Machin-type formulas using arctangent identities converge exponentially faster. We want to formalize convergence rate analysis for these series and characterize what makes some arctangent decompositions optimal.

### Why This Matters

Convergence rate analysis connects number theory (pi approximations) with analysis (series convergence). Formalizing this bridges the gap between the gallery's existing Leibniz formula proof and practical computational aspects of pi computation.

## Known Results

### What's Already Proven

- Leibniz formula π/4 = Σ(-1)^k/(2k+1) — `leibniz-pi` gallery proof
- Alternating series error bound — standard analysis result
- Machin's formula (1706) — classical identity

### What's Still Open

- Formal characterization of optimal arctangent decompositions
- Tight error bounds for specific Machin-type formulas in Lean

### Our Goal

Formalize the O(1/n) convergence rate of the Leibniz series and prove that Machin-type identities achieve exponential convergence. Prove at least one Machin identity.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| leibniz-pi | Direct parent — proves the formula | Alternating series, arctangent |
| geometric-series | Convergence rate techniques | Series bounds |
| harmonic-divergence | Comparison series | Asymptotic analysis |

## Initial Thoughts

### Potential Approaches

1. **Alternating Series Estimation**: Use the Leibniz criterion error bound |S - S_n| ≤ |a_{n+1}| = 1/(2n+3) to prove O(1/n)
   - Why it might work: Direct from Mathlib's alternating series lemma
   - Risk: Low — straightforward

2. **Machin Identity via arctan addition**: Prove arctan(1/5) identity, then derive convergence from Taylor remainder
   - Why it might work: Machin's identity is elementary
   - Risk: Taylor remainder formalization may need work

### Key Difficulties

- Connecting the abstract convergence to concrete rates
- Formalizing "exponential convergence" precisely

### What Would a Proof Need?

- Key lemma 1: Alternating series error bound (likely in Mathlib)
- Key lemma 2: arctan addition formula
- Key lemma 3: Taylor remainder for arctan at small arguments
- Technical requirements: Real analysis, series convergence in Mathlib

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Alternating series estimation is well-supported in Mathlib
- Machin's identity is elementary algebra
- Convergence rate is a direct computation

## References

### Mathlib
- `Mathlib.Analysis.SpecificLimits.Basic` — convergence bounds
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan` — arctan properties
- `Mathlib.Topology.Algebra.InfiniteSum` — series convergence

## Metadata

```yaml
tags:
  - analysis
  - convergence
  - pi-computation
  - series
related_proofs:
  - leibniz-pi
  - geometric-series
  - harmonic-divergence
difficulty: medium
source: gallery-gap
created: 2026-03-11
```
