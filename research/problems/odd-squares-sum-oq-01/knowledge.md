# odd-squares-sum-oq-01 — Sum of Squares of the First n Odd Numbers

**Statement:** ∑_{k<n} (2k+1)² = n(2n−1)(2n+1)/3  (i.e. 1² + 3² + ⋯ + (2n−1)²).

**Status:** COMPLETED (verified, 0 axioms, 0 sorries).

## Summary

Odd-indexed companion of the square-pyramidal identity ∑k² = n(n+1)(2n+1)/6.
Mathlib has the square-pyramidal form but not this odd variant. Proved twice:
the division-free exact ℕ identity `3·∑(2k+1)² + n = 4n³` (additive, so the
inductive step is a single `ring`), and the classical rational closed form
over ℚ.

## Session 2026-06-25 (Session 1) — FRESH

**Mode:** FRESH
**Outcome:** completed

### What I Did
- Verified the formula numerically (n=0..7): ∑ matches n(2n−1)(2n+1)/3 and 3·∑+n = 4n³.
- Wrote `proofs/Proofs/OddSquaresSum.lean` with two theorems.
- `three_mul_sum_odd_squares`: `3·∑(2k+1)² + n = 4n³` by induction; step closes
  by reassociating to expose the hypothesis cluster `3·∑+m` then `ring`.
- `sum_odd_squares_rat`: `∑(2k+1)² = n(2n−1)(2n+1)/3` over ℚ; step is
  `sum_range_succ; push_cast; ring`.
- Compiled offline via `lake env lean` (Docker daemon down): exit 0.
- `#print axioms` for both: only propext / Classical.choice / Quot.sound → axiom-free.
- Added gallery data (meta.json, annotations.json); `pnpm annotations:validate`
  reports no errors for this proof.

### Key Findings
- "Clear the denominator additively": rewriting f(n)/c as c·∑ + (linear) =
  (polynomial) removes both division and truncated ℕ subtraction, collapsing the
  inductive step to one `ring` call.
- The ℚ form is cleanest for the headline division statement; `push_cast`
  handles the ↑(m+1) cast automatically.

### Files Modified
- proofs/Proofs/OddSquaresSum.lean (new, 74 lines)
- src/data/proofs/odd-squares-sum-oq-01/{meta,annotations}.json (new)
- src/data/research/problems/odd-squares-sum-oq-01.json (new)

### Next Steps
- Same pattern for ∑(2k+1)³ = n²(2n²−1) (odd-cubes-sum-oq-01, ℕ-integral RHS).
- Derive as ∑_{j<2n} j² − 4∑_{k<n} k² from Mathlib's square-pyramidal identity.
