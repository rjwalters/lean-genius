# Knowledge Base: Erdős #263 - Irrationality Sequences

## Problem Summary

**Erdős #263**: A sequence (aₙ) of positive integers is an *irrationality sequence* if for every
sequence (bₙ) with bₙ/aₙ → 1, the sum Σ 1/bₙ is irrational.

**Questions**:
1. Is aₙ = 2^{2^n} an irrationality sequence?
2. Must every irrationality sequence satisfy aₙ^{1/n} → ∞?

**Status**: OPEN. Kovač-Tao (2024) established that sequences with aₙ₊₁/aₙ² → 0 are NOT
irrationality sequences. Both original questions remain open.

---

## Session 2026-04-13 (Session 1) — Initial Survey + First Proof

**Mode**: FRESH (EMPTY knowledge tier)
**Outcome**: progress — proved doubleExp_not_folklore_growth

### What I Found

The stub file `proofs/Proofs/Stubs/Erdos263Problem.lean` already existed (265 lines, 7 sorries, 0 axioms)
with the full mathematical framework:
- `IsIrrationalitySequence`: definition (Part II)
- `doubleExp`: 2^{2^n} sequence (Part II)
- `HasFolkloreGrowth`, `HasSuperexponentialGrowth`: growth conditions (Parts III-IV)
- `HasKovacTaoCondition`: the 2024 negative result condition (Part V)
- 2 proved theorems: `doubleExp_square_growth` (a_{n+1}=a_n²), `doubleExp_strictly_increasing`
- 1 proved theorem: `doubleExp_convergent` (Σ 1/2^{2^n} converges by geometric comparison)

### What I Proved

**`doubleExp_not_folklore_growth`**: ¬HasFolkloreGrowth doubleExp

Key insight: `(2^{2^n})^{1/2^n} = 2^{(2^n)*(1/2^n)} = 2^1 = 2` — the function is constantly 2,
which cannot tend to ∞.

Proof technique: `rpow_natCast` + `rpow_mul` to compute the exponent, then `Filter.tendsto_atTop`
to extract the contradiction (constant 2 can't be ≥ 3 eventually).

Also: `characterization_gap` depends on this theorem (proves ∃ a with superexponential but not
folklore growth — witnessing with doubleExp). Since `doubleExp_superexponential` still has sorry,
`characterization_gap` still has sorry.

### Files Modified

- `proofs/Proofs/Stubs/Erdos263Problem.lean` (265 → 285 lines, 7 → 6 sorries)
- `src/data/proofs/erdos-263/meta.json` (sorries 7→6, lineCount 265→285)
- `src/data/research/problems/erdos-263.json`

### Remaining Sorries (6)

1. `folklore_irrationality`: aₙ^{1/2^n} → ∞ ⟹ Σ 1/aₙ irrational (deep)
2. `kovac_tao_not_irrationality`: The 2024 negative result (deep, non-trivial)
3. `positive_condition_irrationality`: liminf aₙ₊₁/aₙ^{2+ε} > 0 ⟹ irrationality sequence (deep)
4. `factorial_no_folklore_growth`: ¬HasFolkloreGrowth factorial_seq (routine)
5. `doubleExp_superexponential`: HasSuperexponentialGrowth doubleExp (routine analysis)
6. `truncation_insufficient`: Any finite truncation loses irrationality info (structural)

### Next Steps

1. Prove `doubleExp_superexponential`: (2^{2^n})^{1/n} = 2^{2^n/n} → ∞ since 2^n/n → ∞
2. Prove `factorial_no_folklore_growth`: (n!)^{1/2^n} → 1 ≠ ∞ (Stirling or direct estimate)
3. Submit remaining deep sorries to Aristotle (folklore, KT condition, positive condition)
