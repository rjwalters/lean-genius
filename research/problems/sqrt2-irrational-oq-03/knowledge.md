# Problem: Irrationality of nth Roots of Non-Perfect Powers

**ID**: sqrt2-irrational-oq-03
**Status**: COMPLETE
**Tier**: B → A (upgraded on completion)
**Significance**: 7/10 | **Tractability**: 7/10

## Problem Statement

For any integers n ≥ 2 and m ≥ 1, if m is not a perfect nth power (no integer k
satisfies k^n = m), then the nth root m^(1/n) is irrational.

This is the natural generalization of the classical √2 irrationality proof to all roots.

## Proof Location

**File**: `proofs/Proofs/NthRootIrrational.lean`
**Gallery**: `src/data/proofs/nth-root-irrational/`
**Status**: 0 sorries, 0 axioms, builds in Docker (Mathlib v4.26.0)

## Key Approach

Uses Mathlib's `irrational_nrt_of_notint_nrt` with a 3-step pattern:
1. Power identity: (m^(1/n))^n = m
2. Not-an-integer: m^(1/n) ∉ ℤ when m is not a perfect nth power (by contrapositive)
3. Conclude via `irrational_nrt_of_notint_nrt`

## Session 2026-02-08 (Session 1) - Complete Proof via Mathlib

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Created `proofs/Proofs/NthRootIrrational.lean` with general theorem + 15 corollaries
- Built general theorem `irrational_nthRoot` using `irrational_nrt_of_notint_nrt`
- Proved "not a perfect power" lemmas for: 2,3,5 (squares), 2,3,5 (cubes), 2,3 (4th powers), 2 (5th powers)
- Proved corollaries: √2,√3,√5, ∛2,∛3,∛5, ⁴√2,⁴√3, ⁵√2
- Fixed /-! docstrings → /- for Aristotle parser compatibility
- Created gallery entry `src/data/proofs/nth-root-irrational/`

### Key Findings

- `irrational_nrt_of_notint_nrt` (Mathlib.NumberTheory.Real.Irrational) is the key tool
- For odd powers: k ≤ 0 implies k^n ≤ 0, contradicting k^n = m > 0
- For even powers: Int.natAbs_sq reduces to natural number case where bounds are simpler
- `nlinarith` handles polynomial bounds (k ≥ 2 → k^n ≥ 2^n)
- `interval_cases` resolves bounded integer case analysis elegantly

### Files Modified

- `proofs/Proofs/NthRootIrrational.lean` (created)
- `src/data/proofs/nth-root-irrational/` (gallery entry, created)

### Next Steps

None - proof is complete.

## Session 2026-02-21 (Session 2) - Housekeeping

**Mode**: FRESH (re-claimed because pool showed available)
**Outcome**: completed

### What I Did

- Rediscovered proof was already complete (NthRootIrrational.lean, 0 sorries)
- Gallery entry confirmed complete (src/data/proofs/nth-root-irrational/)
- Updated candidate pool to mark as completed
- Created this knowledge.md

### Key Findings

- Problem was completed 2026-02-08 but pool entry wasn't updated
- The src/data/research/problems/sqrt2-irrational-oq-03.json was deleted in commit feeb8c1c9 as part of format migration, but pool wasn't updated
