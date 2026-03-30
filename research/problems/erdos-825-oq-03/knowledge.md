# Erdős #470 OQ-03: Odd Weird Numbers

**Problem**: Do odd weird numbers exist? Are there infinitely many primitive weird numbers?
**Status**: IN-PROGRESS (3 axioms, 0 sorries)

## Current State

- **File**: `proofs/Proofs/Erdos470Problem.lean` (~346 lines)
- **Axioms**: 3 (liddy_riedl_6_primes, melfi_conditional, benkoski_erdos_density)
- **Proved**: 12 theorems including smallest_weird_is_70, odd_weird_gt_945, seventy_is_primitive_weird
- **Key results**: native_decide verifications for 70 being weird, 945 being semiperfect

## Session 2026-03-30 (Session 1) - Eliminate nthPrime axiom

**Mode**: FRESH (RICH knowledge, score 18)
**Outcome**: progress (4A→3A, 1 axiom eliminated)

### What I Did
- Replaced `axiom nthPrime : ℕ → ℕ` with `noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n`
- `Nat.nth` is Mathlib's standard function for the n-th element satisfying a predicate
- Updated meta.json and research problem JSON

### Key Findings
- `nthPrime` was a trivially eliminable axiom — Mathlib already provides the exact function
- The remaining 3 axioms are all deep published results requiring sieve theory or analytic number theory
- The file has excellent native_decide proofs for small cases (70 weird, 945 semiperfect, etc.)

### Files Modified
- `proofs/Proofs/Erdos470Problem.lean` (344→346 lines, -1 axiom, +1 def)
- `src/data/proofs/erdos-470/meta.json` (axiomCount: 4→3)
- `src/data/research/problems/erdos-825-oq-03.json` (knowledge updated)

### Next Steps
- Verify build when Docker available
- Remaining 3 axioms are deep results — not eliminable from Mathlib
