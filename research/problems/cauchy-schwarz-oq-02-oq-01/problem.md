# Problem: Parseval's Identity for Fourier Coefficients

**Slug**: cauchy-schwarz-oq-02-oq-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_n |\hat{c}_n|^2 = \|f\|^2
$$

### Plain Language

Extension of the verified cauchy-schwarz-oq-02. Parseval's identity connects L² norm to Fourier coefficient norms. Parent proof is fully verified (0 sorries, 0 axioms).

### Why This Matters

See `src/data/proofs/cauchy-schwarz-oq-02/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `cauchy-schwarz-oq-02` provides the foundation
- sorries to fill: 0 (plus any axioms — check source proof)

### Our Goal

New formalization problem (not completing a sorry). Build on the L² Pythagorean theorem and polarization identity already in cauchy-schwarz-oq-02. Check Mathlib's FourierAnalysis module.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `cauchy-schwarz-oq-02` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Medium

## Metadata

```yaml
tags:
  - analysis
  - cauchy-schwarz
  - fourier
  - l2-spaces
  - parseval
related_proofs:
  - cauchy-schwarz-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-03
```

**Significance**: 7/10
**Tractability**: 6/10
