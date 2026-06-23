# Problem: Complex-Valued Hölder via Nnnorm — Next Extensions

**Slug**: cauchy-schwarz-integral-oq-01-oq-03
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Context

The gallery proof `cauchy-schwarz-integral-oq-01-oq-03` (verified, 0 sorries) establishes:

> The nnnorm approach to Hölder's inequality generalizes uniformly to any `NormedField`
> (ℝ, ℂ, or any valued field). The complex case is a trivial corollary via nnnorm
> multiplicativity.

This problem workspace targets the two open questions raised by that proof.

### Open Questions to Pursue

**OQ-A** (primary): Can the snorm-based Hölder inequality

$$\|fg\|_{L^1} \leq \|f\|_{L^p} \cdot \|g\|_{L^q}$$

be formalized for `NormedField` scalars in the same uniform way as the nnnorm version?

**OQ-B** (secondary): Does the same nnnorm approach extend to Hölder's inequality in
Banach space-valued settings (Bochner integral)?

### Plain Language

The existing proof uses `nnnorm` (non-negative norm values, `ℝ≥0`-valued) to handle both
real and complex cases uniformly. The question is whether the `snorm`-based Hölder (which
Mathlib uses for `MeasureTheory.Lp` spaces) can be given the same treatment without
case-splitting on ℝ vs ℂ.

### Why This Matters

Uniform formulations for any `NormedField` reduce duplication in the `MeasureTheory.Lp`
API and could simplify future extensions to p-adic or other valued field contexts.

## Known Results

### What's Already Proven

- `NNNorm.inner_le_nnorm_mul_nnorm` — Cauchy-Schwarz via nnnorm (gallery)
- `cauchy-schwarz-integral-oq-01-oq-03` (gallery, verified) — Hölder for NormedField via nnnorm
- `MeasureTheory.inner_le_Lnorm_mul_Lnorm` — Mathlib snorm Hölder (real-valued)

### What's Still Open

- Uniform snorm-based Hölder for `NormedField` scalars
- Bochner-integral Hölder via nnnorm for Banach-valued functions

### Our Goal

Determine which of OQ-A or OQ-B is more tractable and attempt a Lean formalization.
OQ-A is preferred (direct snorm extension); OQ-B is harder (needs Bochner integral).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cauchy-schwarz-integral-oq-01-oq-03` | Direct parent — nnnorm Hölder for NormedField | nnnorm, NNReal algebra |
| `cauchy-schwarz-integral-oq-01` | Original Cauchy-Schwarz integral | ENNReal, snorm |
| `cauchy-schwarz-integral` | Base Cauchy-Schwarz for L² | inner product space |

## Initial Thoughts

### Potential Approaches

1. **snorm lifting via nnnorm** (OQ-A):
   - Express `snorm f p μ` in terms of `∫ ‖f x‖₊^p ∂μ` (which uses nnnorm)
   - Apply the existing nnnorm Hölder to get the bound
   - Why it might work: snorm is defined via nnnorm integrals already
   - Risk: `NNNorm` → `Norm` casting may need careful bounding

2. **Bochner Hölder** (OQ-B):
   - Extend `MeasureTheory.Lp.inner_le_Lnorm_mul_Lnorm` to Banach-valued case
   - Requires: Pettis measurability, weak integration lemmas
   - Why it might work: nnnorm still works for Banach norms
   - Risk: Significantly more Mathlib infrastructure required

### Key Difficulties

- `snorm` in Mathlib is `ℝ≥0∞`-valued; bridging to `NNReal` requires care at `p = ∞`
- Mathlib's existing `snorm` Hölder is specialized to `ℝ`; NormedField version may not exist

### What Would a Proof Need?

- Key lemma: `snorm (f * g) 1 μ ≤ snorm f p μ * snorm g q μ` for NormedField
- Technical: `1/p + 1/q = 1` hypothesis in ENNReal arithmetic
- Mathlib: `MeasureTheory.snorm_mul_le` or similar

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The nnnorm framework is already established in the gallery
- Mathlib has `MeasureTheory.inner_le_Lnorm_mul_Lnorm` as a model
- The main gap is generalizing from ℝ to NormedField coefficients
- OQ-A should be doable in a few days; OQ-B is harder (week+)

**Estimated Effort**:
- Exploration: 2-4 hours (read Mathlib snorm API)
- OQ-A: 2-4 days
- OQ-B: 1-2 weeks

## References

### Mathlib
- `Mathlib.MeasureTheory.Function.LpSpace` — snorm, Lp spaces
- `Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace` — Cauchy-Schwarz
- `Mathlib.Analysis.NormedSpace.BoundedLinearMaps` — Banach-valued integration

## Metadata

```yaml
tags:
  - analysis
  - inequalities
  - holder
  - nnnorm
  - lp-spaces
related_proofs:
  - cauchy-schwarz-integral-oq-01-oq-03
  - cauchy-schwarz-integral-oq-01
  - cauchy-schwarz-integral
difficulty: medium
source: gallery-gap
created: 2026-04-23
```

**Significance**: 7/10
**Tractability**: 6/10
