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

## Session 2026-04-14 (Session 2) — Prove factorial_no_folklore_growth

**Mode**: REVISIT (MODERATE knowledge tier)
**Outcome**: progress — proved `factorial_no_folklore_growth` (sorries 5→4)

### What I Did

Proved `factorial_no_folklore_growth : ¬HasFolkloreGrowth factorial_seq` via two helper lemmas:

**`succ2_le_two_pow_pow`**: n + 2 ≤ 2^(2^n) for all n.
- Base: 0 + 2 = 2 ≤ 2^1 = 2 ✓
- Step: 2^(2^(m+1)) = 2^(2^m) * 2^(2^m) ≥ 2 * (m+2) ≥ m+3 ✓

**`factorial_le_two_pow_pow`**: (n+1)! ≤ 2^(2^n) for all n.
- Base: 1! = 1 ≤ 2^1 = 2 ✓
- Step: (m+2)! = (m+2) * (m+1)! ≤ 2^(2^m) * 2^(2^m) = 2^(2^(m+1)) ✓

**Main theorem**: If `HasFolkloreGrowth factorial_seq` then eventually `((n+1)!)^{1/2^n} ≥ 3`.
But `(n+1)! ≤ 2^(2^n)` implies `((n+1)!)^{1/2^n} ≤ (2^(2^n))^{1/2^n} = 2 < 3`. Contradiction.

### Key Lean Techniques

- `Filter.tendsto_atTop.mp h 3` → eventuality argument
- `Real.rpow_le_rpow` to propagate the factorial bound through rpow
- `← rpow_natCast` + `← rpow_mul` + `push_cast` + `div_self` to compute `(2^{2^N})^{1/2^N} = 2`
- `Nat.mul_le_mul` for both helper inductions

### Remaining Sorries (4)

1. `folklore_irrationality`: aₙ^{1/2^n} → ∞ ⟹ Σ 1/aₙ irrational — requires Mahler-type criterion (DEEP, not in Mathlib)
2. `kovac_tao_not_irrationality`: The 2024 negative result — requires greedy Egyptian fraction construction (DEEP)
3. `positive_condition_irrationality`: liminf aₙ₊₁/aₙ^{2+ε} > 0 ⟹ irrationality sequence (DEEP)
4. `truncation_insufficient`: ∀N, ∃ sequences agreeing on N terms with opposite irrationality status (DEEP)

All 4 remaining sorries reflect genuinely open or deep mathematics beyond current Mathlib.

### Files Modified

- `proofs/Proofs/Stubs/Erdos263Problem.lean` (285 → ~345 lines, 5 → 4 sorries)
- `src/data/proofs/erdos-263/meta.json` (sorries 5→4, lineCount updated)
- `src/data/research/problems/erdos-263.json` (knowledge updated)

---

## Session 2026-04-14 (Session 3) — Meta.json Sync (4 sorries, 385 lines)

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: maintenance — fixed stale meta.json (sorries 5→4, lineCount 342→385)

### What I Did

- Audited the current state: Lean file has 4 sorries (lines 83, 141, 154, 336); meta.json
  still said 5 sorries with `factorial_no_folklore_growth` listed (proved in session 2 / PR #10766)
- PR #10717 (mechanic sorry-count sync, merged before #10766) re-introduced the stale count
- Fixed all three `sorries` fields and both `lineCount` fields in meta.json
- Confirmed: no new mathematical progress is possible without Mathlib contributions for the
  4 remaining deep sorries

### Remaining Sorries (4, unchanged)

All 4 require mathematics not currently in Mathlib:
1. `folklore_irrationality`: Mahler-type irrationality criterion
2. `kovac_tao_not_irrationality`: Kovač-Tao 2024 Egyptian fraction construction
3. `positive_condition_irrationality`: liminf growth → irrationality sequence
4. `truncation_insufficient`: requires concrete irrationality / non-irrationality sequence witnesses

### Files Modified

- `src/data/proofs/erdos-263/meta.json` (sorries 5→4, lineCount 342→385)

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
