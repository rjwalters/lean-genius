# Current State

**Phase**: ACT
**Since**: 2026-05-01
**Iteration**: 3

## Current Focus

Correctness layer complete. Decide whether to pursue size-reduction lemma
(needed for asymptotic complexity bound) or treat current correctness layer
as the final scope of this open question.

## Active Approach

Session 2 outcome: Path A (correctness only) implemented in
`BinaryGcdOQ03OQ02.lean` (~340 lines, 0 sorries on the correctness layer).
Recursive `hgcdMatrix` is fuel-indexed (avoiding the size-reduction proof
obligation in the definition); det ±1 invariant is proved by induction on
fuel; GCD preservation follows from `cofactor_apply_gcd`.

## Blockers

- **Complexity claim**: O(M(n)·log n) remains unfalsifiable in Lean.
  Requires Mathlib bit-complexity model + fast multiplication. Multi-
  thousand-line foundational project; explicitly out of scope.
- **Size-reduction lemma**: stated as `hgcdMatrix_size_reduction`
  placeholder. The lemma asserts that applying the recursively computed
  HGCD matrix halves the bitsize of (a, b) up to an O(1) constant. Stehlé
  and Zimmermann (2004) give explicit constants for the binary-recursive
  variant. Estimated effort: 150-300 self-contained Lean lines for a
  precise statement and proof, depending on the bitsize formulation
  chosen.

## Next Action

1. (Optional) Prove the size-reduction lemma. Pick a bitsize measure
   (`Nat.log 2 + 1`), state advance for one HGCD step, recursive
   composition for two steps. Self-contained — does not need new Mathlib.
2. (Optional) Wire `hgcdMatrix` into a top-level recursive GCD: take input
   pair, iterate `hgcdMatrix` until below threshold, run `euclidGcd` at
   the leaf. Prove correctness by composing `hgcdMatrix_preserves_gcd`
   with `euclidGcd_eq_gcd`. ~50-100 lines.
3. (Deferred — separate initiative) Bit-complexity O(M(n)·log n) requires
   Mathlib upstream work (fast multiplication, bit-complexity model).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Path A: fuel-indexed correctness, succeeded)
