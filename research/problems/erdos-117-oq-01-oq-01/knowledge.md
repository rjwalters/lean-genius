# erdos-117-oq-01-oq-01: Exponential Base Implies Exponential Behavior

**Status**: COMPLETED (0 sorries, 0 axioms beyond Erdos117OQ01)
**Phase**: COMPLETED
**File**: `proofs/Proofs/Erdos117OQ01OQ01.lean`

## Problem Statement

OQ-01-OQ-01: Can `base_implies_behavior` from Erdos117OQ01.lean be proved?
If lim log(h(n))/n = log c (with c > 1), does h(n) behave like cⁿ?

**Answer**: YES, with a correction to the ε range.

## Session 2026-04-21 (Session 1) - Complete Proof

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Identified the sorry in `Erdos117OQ01.base_implies_behavior`
2. Discovered a subtle issue: the original `ExponentialBehavior c` definition
   uses ∀ ε > 0, but for ε > 2c the lower bound (c-ε)^n ≤ h n fails for even n
   (as noted in the parent file's comment)
3. Defined `ExponentialBehaviorCorrect c` restricting to ε ∈ (0, c)
4. Proved `base_implies_behavior_correct` using exp/log monotonicity
5. Added corollary connecting to `submultiplicative_implies_convergence`

### Key Findings

- **Sign issue**: `(c - ε)^n` for even n when c - ε < 0 equals `(ε - c)^n`, which
  grows faster than h(n) ≈ cⁿ if ε - c > c. The original ExponentialBehavior def
  is technically unprovable as stated for large ε.
- **Fix**: Restrict to ε ∈ (0, c) so c - ε > 0 always.
- **Proof core**: `log(h n)/n → log c` ↔ for small δ, log(h n) ≈ n·log c. Then
  exp both sides: h n ≈ cⁿ. Key API: `Real.exp_log`, `Real.log_pow`, `Real.exp_le_exp`.
- **`ge_of_tendsto`**: used to establish L ≥ log c₁ > 0 from Pyber's lower bound.
- **Pyber bounds**: c₁^n ≤ h n gives the limit L is bounded below by log c₁ > 0.

### Files Modified

- `proofs/Proofs/Erdos117OQ01OQ01.lean` (new file)
- `proofs/Proofs.lean` (added import)

### Mathematical Insight

The exponential base theorem follows from the general principle: if a sequence
converges (here log(h n)/n → log c), then eventually the terms stay within any
δ-neighborhood. Taking δ to be the log-gap at c ± ε converts the convergence to
a two-sided exponential bound via the monotone exp function.

### Next Steps

None — proof is complete. The corrected ExponentialBehaviorCorrect could be
contributed back to improve the ExponentialBehavior definition in OQ01.
