# Erdős #1014 OQ-01: R(3,l+1)/R(3,l) → 1

## Problem Summary

**Goal**: Prove R(3,l+1)/R(3,l) → 1 as l → ∞ (k=3 case of Erdős Problem #1014).

**Status**: ESSENTIALLY COMPLETE — 1 routine sorry remaining.

**Key Insight**: The Ramsey recurrence R(3,l+1) ≤ R(3,l) + R(2,l+1) = R(3,l) + (l+1) bounds the increment linearly, while the Kim-Shearer lower bound shows R(3,l) = Ω(l²/log l). The ratio R(3,l+1)/R(3,l) - 1 ≤ O(log l / l) → 0.

This shows the Θ(l²/log l) bounds DO suffice for k=3 when combined with the recurrence. Only the lower bound is needed.

## Session 2026-03-24 (Session 1) - Initial Proof

**Mode**: FRESH
**Outcome**: progress (essentially complete)

### What I Did
- Selected erdos-1014-oq-01 from candidate pool (all available problems had knowledge score 0)
- Identified the key mathematical insight: recurrence provides O(l) increment bound
- Created `proofs/Proofs/Erdos1014OQ01.lean` (169 lines)
- Proved 3 theorems:
  1. `increment_bound`: R(3,l+1) ≤ R(3,l) + (l+1) (fully proved)
  2. `ratio_abs_eq`: |R'/R - 1| = (R'-R)/R (fully proved)
  3. `erdos_1014_k3_ratio_convergence`: main theorem (proved modulo analysis lemma)
- 1 sorry on `eventually_ratio_small`: routine analysis (log l/l → 0)
- Created gallery entry with meta.json, index.ts, annotations.json
- Docker build passes

### Key Findings
- The recurrence R(k,l+1) ≤ R(k,l) + R(k-1,l+1) is the crucial tool — it provides an increment bound independent of the Θ bounds
- For k=3: R(k-1,l+1) = R(2,l+1) = l+1 (trivial), giving a linear increment bound
- Only the LOWER bound on R(3,l) is needed, not the upper bound
- Mathlib API spelunking for `isLittleO_log_rpow_atTop` → `eventually` conversion was unsuccessful in session

### Files Modified
- `proofs/Proofs/Erdos1014OQ01.lean` (new, 169 lines)
- `src/data/proofs/erdos-1014-oq-01/` (new gallery entry)
- `src/data/research/problems/erdos-1014-oq-01.json` (updated)
- `.lean/state/candidate-pool.json` (status → in-progress)

### Next Steps
- Prove `eventually_ratio_small` using Mathlib's `isLittleO_log_rpow_atTop` with p=1
- Consider creating Aristotle companion file for the analysis sorry
- Consider extending approach to k=4: R(4,l+1) - R(4,l) ≤ R(3,l+1) = O(l²/log l)
