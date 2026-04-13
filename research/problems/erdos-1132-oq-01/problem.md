# Problem: Erdős #1132 OQ-01: Witness Points for Bernstein's Density Theorem

**Slug**: erdos-1132-oq-01
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a node sequence $(x_1, x_2, \ldots) \subset [-1,1]$, define the $n$-th Lebesgue function:
$$\Lambda_n(x) = \sum_{k=1}^n \left| \ell_k^{(n)}(x) \right|$$
where $\ell_k^{(n)}$ are the Lagrange basis polynomials for nodes $x_1, \ldots, x_n$.

**Bernstein's Theorem (1931, axiomatized)**: For any infinite node sequence, the set of
"good points" (where $\Lambda_n(x)/\log n \to \infty$) is dense in $[-1,1]$.

**OQ-01**: Can the `bernstein_density_theorem` or `erdos_max_theorem` axioms in
`Erdos1132Problem.lean` be reduced via Lean formalization of the underlying classical analysis?

More concretely: can we prove a version of Erdős's 1961 result (max of Lebesgue function
> (2/π)log n - C) from Mathlib's polynomial and analysis infrastructure?

### Plain Language

The Lebesgue function measures how badly Lagrange interpolation can amplify errors. Bernstein
(1931) showed that for ANY choice of interpolation nodes, the Lebesgue constant grows like
log(n) at a dense set of points — you can't spread the badness out evenly.

The parent proof (`erdos-1132`) axiomatizes this as `bernstein_density_theorem`. OQ-01 asks:
can we formally construct a witness point and prove the divergence using Mathlib's analysis
machinery? The axiom `erdos_max_theorem` (Erdős 1961: max of Lebesgue function > (2/π)log n)
is a weaker but potentially more tractable starting point.

### Why This Matters

1. **Axiom reduction**: Reduces `axiomCount` of `erdos-1132` from 2 toward 0
2. **Analysis infrastructure**: Tests Mathlib's polynomial + measure theory capabilities
3. **Foundational**: Bernstein's theorem is a classical result; formalization would be
   valuable for the wider Mathlib community (approximation theory gap)

## Known Results

### What's Already Proven (in gallery)

- `lagrangeBasis_sum_eq_one` — partition of unity for Lagrange basis (proved in parent)
- `lebesgueFunction_ge_one` — Lebesgue function ≥ 1 everywhere (proved in parent)
- Equidistant nodes have exponentially growing Lebesgue constants (proved in parent)
- `Lagrange.sum_basis` — Mathlib's Lagrange interpolation sum

### What's Axiomatized

- `bernstein_density_theorem` — density of "good" (diverging) points
- `erdos_max_theorem` — max of Lebesgue function > (2/π)log(n) - 10

### Our Goal

Focus first on `erdos_max_theorem`: prove a version of Erdős's 1961 result that the maximum
of the Lebesgue function over [-1,1] grows at least logarithmically. This is weaker than
Bernstein's density result and may be formalizable using Chebyshev polynomial theory or
orthogonality arguments in Lean 4.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-1132` | Parent proof with both axioms | Lagrange interpolation definitions |
| `erdos-1129` | Optimal Lagrange interpolation nodes | Approximation theory |

## Initial Thoughts

### Potential Approaches

1. **Approach A: Prove `erdos_max_theorem` via orthogonality / Chebyshev**
   - Lower bound on max Λ_n follows from the norm of the interpolation projector
   - Chebyshev polynomials minimize max |ω(x)|; dual argument gives Λ_n lower bound
   - Risk: Mathlib's Chebyshev / operator norm infrastructure may be insufficient

2. **Approach B: Construct witness for equidistant nodes at x = 0**
   - More concrete: prove Λ_n(0) → ∞ for equidistant nodes $x_k = -1 + 2k/(n-1)$
   - Simpler target; avoids density argument; yields a constructive proof
   - Could become a standalone gallery entry

3. **Approach C: Formalize via L∞ projection norm argument**
   - Use that the L∞ norm of the Lagrange interpolation operator grows like log n
   - Follows from functional analysis (Banach-Steinhaus for Lagrange projectors)
   - Risk: abstract functional analysis over C[-1,1] is not well-formalized in Mathlib

### Key Difficulties

- Mathlib has `Polynomial.lagrange` but limited analysis tools for bounding operator norms
- The Lebesgue constant (sup over [-1,1]) requires `Real.iSup` machinery and continuity
- Bernstein's proof uses classical analysis tools (uniform boundedness or direct estimates)

### What Would a Proof Need?

- Chebyshev polynomial properties: `Polynomial.Chebyshev.T`, orthogonality
- `Finset.card_le_iff` style arguments for node counts
- `Real.iSup_le` / `Real.le_iSup` for bounding the supremum
- Possibly: `MeasureTheory.inner_le_iff` for L² orthogonality arguments

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- `erdos_max_theorem` (weaker: just the maximum, not density) more tractable
- Mathlib has `Polynomial.lagrange`, `Polynomial.Chebyshev`, `Polynomial.eval`
- Classical analysis proof (1961) uses elementary but involved Fourier/Chebyshev estimates
- Lean 4 approximation theory is underdeveloped — likely requires new helper lemmas

**Estimated Effort**:
- Exploration (OBSERVE/ORIENT): 1-2 sessions
- Approach B (concrete equidistant case): 2-3 sessions — most tractable path
- Full `erdos_max_theorem` proof: 4-6 sessions

## References

### Papers
- Bernstein, S.N. (1931) — Density theorem for Lagrange interpolation
- Erdős, P. (1961) — Lower bound for Lebesgue constants: max Λ_n ≥ (2/π)log n - C
- Cheney, E.W. "Introduction to Approximation Theory" — classical reference

### Mathlib
- `Mathlib.LinearAlgebra.Lagrange` — Lagrange interpolation definitions
- `Mathlib.RingTheory.Polynomial.Chebyshev` — Chebyshev polynomial definitions
- `Mathlib.Analysis.Normed.Group.Basic` — normed spaces for L∞ bounds
- `Mathlib.Topology.ContinuousFunction.Polynomial` — polynomial eval continuity
- `Mathlib.Analysis.SpecificLimits.Basic` — log growth estimates

## Metadata

```yaml
tags:
  - approximation-theory
  - lagrange-interpolation
  - lebesgue-function
  - polynomial-theory
  - analysis
  - erdos
related_proofs:
  - erdos-1132
  - erdos-1129
difficulty: medium
source: gallery-gap
created: 2026-04-05
```
