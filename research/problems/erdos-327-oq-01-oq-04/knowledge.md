# Knowledge: erdos-327-oq-01-oq-04

## Overview

Sub-question of Erdős #327 OQ-01 (parametrization). Proves D(N) ≥ ⌊N/6⌋
using explicit witness family {(3k, 6k) : 1 ≤ k ≤ ⌊N/6⌋}.

## Session 2026-04-13 — PROVED

**Mode**: FRESH
**Outcome**: All theorems proved (0 sorries)

### What I Did

Created new Lean file `Erdos327OQ01OQ04.lean` proving:
1. `threeK_sixK_dvd`: (3k+6k) | (3k·6k) since 9k | 18k² = 9k·2k
2. `witnessFamily_subset`: each (3k, 6k) in [1,N] satisfies both elements ≤ N and (3k+6k)|(3k·6k)
3. `witnessFamily_card = N/6`: via `Finset.card_image_of_injective` + `Finset.Nat.card_Icc`
4. `sumDvdProdPairs_lowerBound`: N/6 ≤ D(N) by witnessFamily ⊆ sumDvdProdPairs N
5. `sumDvdProdPairs_unbounded`: D(N) → ∞ as corollary

### Key Lemmas
- `Nat.div_mul_le_self N 6 : N/6 * 6 ≤ N` — for bounding 6k ≤ N
- `Finset.card_image_of_injective` — for counting the witness family
- `Finset.Nat.card_Icc` — for (Finset.Icc 1 m).card = m
- `Finset.card_le_card` — for the subset bound

### Files Created
- `proofs/Proofs/Erdos327OQ01OQ04.lean` (88 lines, 0 sorries)
- `src/data/proofs/erdos-327-oq-01-oq-04/meta.json`

## Key References

- Parent: `src/data/proofs/erdos-327-oq-01/`
- Gallery: Erdős #327
