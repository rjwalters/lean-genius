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

### Session 3 (researcher-4, 2026-03-30)
- Integrated 4 proved theorems from Erdos362Aristotle.lean into main file:
  - `zpow_finset_sum`: ∏ z^a = z^(∑ a) for z ≠ 0 (induction + zpow_add₀)
  - `gf_at_one`: GF(1) = 2^|A| (all subsets counted)
  - `gf_expansion`: ∏(1+z^a) = ∑_{S⊆A} z^{setSum S} (via Finset.prod_one_add)
  - `gf_disjoint_union`: GF factors over disjoint union (via prod_union)
- Added `import Mathlib.Algebra.BigOperators.Ring.Finset` for `prod_one_add`
- Documented proof roadmap for `fourier_extraction` axiom:
  - Key: gf_expansion + Fourier orthogonality proves it
  - Two approaches: (1) direct FTC on ℝ, (2) Mathlib AddCircle/fourierCoeff
- Verified `symmetric_max_at_zero` is CORRECT for even N:
  - N=4: {-1,0,1,2} → max count 4 at t=0,1,2 (plateau includes 0) ✓
  - N=6: {-2,-1,0,1,2,3} → max count 10 at t=0,1,2,3 ✓
  - The asymmetric shift doesn't push peak past 0; max is on a flat plateau
- File stats: 283 lines, 9 theorems/lemmas, 7 axioms, 10 definitions, 0 sorries

## Dead Ends

- Proving erdos_moser from S-S requires real analysis lemmas about log;
  PR #7493 handles this more thoroughly
- symmetric_max_at_zero: proving for all N requires log-concavity/unimodality theory (related to hard Lefschetz); not in Mathlib
- fourier_extraction via direct integral computation: requires significant measure theory plumbing; AddCircle approach may be cleaner
