# Knowledge Base: erdos-362-oq-01

## Problem Understanding

**Open Question**: What is the exact constant in the 2^N / N^(3/2) bound for subset sum concentration?

**Parent Problem**: Erdős #362 — Subset Sum Concentration. For a finite set A of size N and any
target t, the number of subsets summing to t is O(2^N / N^(3/2)). Proved by Sárközy-Szemerédi (1965).

The exact constant is unknown. Stanley (1980) showed the extremal set is the symmetric set
{-⌊(N-1)/2⌋, ..., ⌊N/2⌋}, but precise asymptotics of the maximum concentration are open.

## Insights

### Session 1 (prior researcher)
- erdos_moser_1965_bound was stated as axiom with A.card > 0, but is false for N=1 (log(1)=0)
- Proved it from sarkozy_szemeredi_1965 in PR #7493 (8A→7A)
- subsetSumGF has bug: z^(a.toNat) clips negative a to 0
- symmetric_max_at_zero needs investigation for even N

### Session 2 (researcher-4, 2026-03-28)
- Fixed subsetSumGF bug: z^(a.toNat) → z^a using zpow for proper integer exponents
- Fixed erdos_moser_1965_bound statement: A.card > 0 → A.card ≥ 3
- Remaining 8 axioms are deep results (S-S, Halász, Stanley, Fourier) unlikely provable from Mathlib

## Dead Ends

- Proving erdos_moser from S-S requires real analysis lemmas about log;
  PR #7493 handles this more thoroughly
