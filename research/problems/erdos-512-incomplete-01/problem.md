# Problem: Erdős #512 — Fill Measure Theory Gaps in Littlewood Conjecture Formalization

**Slug**: erdos-512-incomplete-01
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The gallery proof `Proofs/Erdos512Problem.lean` formalizes Littlewood's Conjecture (proved 1981) with two sorries:

**Sorry 1** (line 104): `L1norm_upper_bound`:
```lean
theorem L1norm_upper_bound (A : Finset ℤ) : L1norm A ≤ A.card := by
  sorry -- Requires measure theory
```

**Sorry 2** (line 167): `L2_norm` (Parseval):
```lean
theorem L2_norm (A : Finset ℤ) :
    ∫ θ in Set.Icc 0 1, (expSumNorm A θ)^2 = A.card := by
  sorry -- Parseval's theorem
```

### Plain Language

Two standard gaps in the Littlewood conjecture formalization:
1. L¹ norm ≤ |A| (triangle inequality + |e^{ix}|=1)
2. L² norm squared = |A| (Parseval's identity on [0,1])

Both are classical results; the challenge is finding the right Mathlib API.

### Why This Matters

Closes two concrete gaps in the Erdős #512 formalization. Both are mathematically trivial; the task is purely Lean/Mathlib.

## Known Results

### What's Already Proven
- `L1norm_nonneg`, basic setup of `expSum`, `expSumNorm`, `L1norm`
- Main result as axioms (`konyagin_theorem`, `mcgehee_pigno_smith_theorem`)

### Our Goal
Fill sorries at lines 104 and 167 using Mathlib's measure theory and Fourier analysis.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-512` | Parent proof with sorries at lines 104, 167 |

## Initial Thoughts

### For L1norm_upper_bound
- `norm_integral_le_integral_norm` + triangle inequality
- `‖expSumNorm A θ‖ ≤ ∑ n in A, ‖e^{2πi nθ}‖ = A.card` (since |e^{ix}|=1)
- Mathlib: `Complex.abs_exp_ofReal_mul_I`, `Finset.card_eq_sum_ones`

### For L2_norm (Parseval)
- Expand product, distribute integral, use character orthogonality
- `∫₀¹ e^{2πi(n-m)θ} dθ = if n=m then 1 else 0`
- Mathlib: `MeasureTheory.integral_finset_sum`, Fourier orthogonality

## Tractability Assessment

**Difficulty**: Medium — purely a Mathlib API search problem

**Estimated Effort**:
- L1norm_upper_bound: 1-2 hours
- L2_norm (Parseval): 2-4 hours

## Metadata

```yaml
tags:
  - erdos
  - fourier-analysis
  - measure-theory
  - sorry-completion
  - seeker-selected
related_proofs:
  - erdos-512
difficulty: medium
source: gallery-gap
created: 2026-04-23
```

**Significance**: 8/10
**Tractability**: 5/10
