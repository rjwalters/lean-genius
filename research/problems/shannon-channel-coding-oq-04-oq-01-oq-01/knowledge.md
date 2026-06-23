# Knowledge Base: shannon-channel-coding-oq-04-oq-01-oq-01

## Problem

Prove that the maximum of binary entropy h(p) = -p·log(p) - (1-p)·log(1-p) on [0,1] is log 2, achieved uniquely at p = 1/2.

## Session 2026-04-05 (Session 1)

**Outcome**: COMPLETE. 4 theorems, 0 sorries, 0 axioms. Build successful. PR created.

### What I Did

1. Proved `h_deriv_zero_iff`: h'(p) = log(1-p) - log(p) = 0 iff p = 1/2 (via `congr_arg Real.exp` + `Real.exp_log`)
2. Proved `h_lt_h_half`: h(p) < log 2 for p ∈ (0,1) with p ≠ 1/2 via midpoint decomposition 1/2 = (1/2)p + (1/2)(1-p) + strict concavity from OQ-01 + symmetry h(1-p) = h(p)
3. Proved `h_eq_log_two_iff`: h(p) = log 2 iff p = 1/2 on [0,1] (case split: boundaries use h_zero/h_one, interior uses h_lt_h_half)
4. Proved `hBits_eq_one_iff`: h₂(p) = 1 iff p = 1/2 via `div_eq_one_iff_eq`

### Key Findings

- **Midpoint decomposition pattern**: Write 1/2 = (1/2)p + (1/2)(1-p). Use `h_symm` for h(1-p) = h(p), so the strict concavity RHS collapses to h(p). `StrictConcaveOn.2` with `by norm_num` for the 1/2 + 1/2 = 1 condition.
- **Log injectivity via exp round-trip**: `log(1-p) = log(p) → exp(log(1-p)) = exp(log(p)) → 1-p = p` using `congr_arg Real.exp` + `Real.exp_log`.
- Depends on `ShannonChannelCodingOQ04OQ01` (strict concavity) and `ShannonChannelCodingOQ04` (h_zero, h_one, h_half, h_symm, hBits).

### Files Modified

- `proofs/Proofs/ShannonChannelCodingOQ04OQ01OQ01.lean` (created, 102 lines, 0 sorries)
- `src/data/proofs/shannon-channel-coding-oq-04-oq-01-oq-01/` (meta.json, annotations.json, index.ts)
