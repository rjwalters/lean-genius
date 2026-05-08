# Current State

**Phase**: ACT — Path A chosen post-S17. S18 laid the foundation
(`hgcdMatrixSafe` with runtime safety guard, det+gcd preserved);
S19 wraps Path A as a verified GCD function `hgcdSafeGcd` with
correctness `hgcdSafeGcd a b = Nat.gcd a b`.

**Since**: 2026-05-01
**Iteration**: 19

## Current Focus

Session 19 wraps the Path A foundation (S18 — `hgcdMatrixSafe`) into
an end-to-end verified GCD function `hgcdSafeGcd : ℕ → ℕ → ℕ` with
correctness theorem `hgcdSafeGcd_eq_gcd a b = Nat.gcd a b` (0 sorries,
0 axioms).

The construction is direct: apply `hgcdMatrixSafeOf a b` to `(a, b)`
and take the `Int.gcd` of the column-output pair. Correctness reduces
to `hgcdMatrixSafeOf_preserves_gcd` (S18) by unfolding `apply` and
matching against the existing GCD-preservation theorem.

This closes the operational correctness story for Path A: even where
the unguarded `hgcdMatrix` produces magnitude blowup (S17 PART XIV
showed entries of order 10^268 at `(107, 85)`), the safer variant
returns a unimodular matrix whose column-output GCD agrees with
`Nat.gcd a b`. The runtime size-reduction guard does not need to
fire correctly for THIS theorem to hold.

Path A roadmap remaining (S20+):

1. **S20 — `hgcdMatrixSafe_size_reduction` (positive form)**: prove
   that on inputs `max a b ≥ hgcdThresholdSafe`, when the runtime
   guard fires (compose branch), the column output strictly reduces.
   The guard makes this provable structurally rather than via the
   row-vector invariant lift (which S17 showed is FALSE for the
   unguarded algorithm).

2. **S21+ — recursive Schönhage-style GCD via iteration**: instead
   of a single matrix application, iterate `hgcdMatrixSafe` on the
   reduced pair until below threshold, then dispatch to `Nat.gcd`.
   Termination needs the S20 size-reduction in the compose branch
   plus a fallback handler for the abort branch.

3. **Bit-complexity bound** (`O(M(n)·log n)`): genuinely blocked on
   Mathlib (no fast multiplication, no bit-complexity model).
   Documented; defer until Mathlib lands these.

Status of the proof plan (Sessions 1–19):

1. **Step 1** ✅ (S3, PR #14522): row-vector invariant for
   `lehmerCofactors`. PART V.5.
2. **Step 2a** ✅ (S3, PR #14522): residue monotonicity for
   `lehmerCofactors`. PART V.5.
3. **Step 2b (Lehmer)** ✅ (S4, PR #14881): entry bound for
   `lehmerCofactors` via row-Cramer + sign pattern. PART VI.
4. **Step 3** ✅ (S5, PR #14910): perturbation infrastructure
   (algebraic split + triangle bounds). PART VII.
5. **Row-output composition under `mul`** ✅ (S12, PR #16662):
   `cofactor_mul_row_output` + `cofactor_mul_row_output_natAbs_le`.
   PART VIIc.
6. **Sign-pattern lifting to HGCD** ✅ (S13, PR #16729):
   `hgcdMatrix_has_pattern` via Z/2-graded `cofactor_mul_pattern`.
   PART X.
7. **Row-vector invariant — base + threshold + composition law** ✅
   (S14, PR #16908): `cofactor_mul_row_invariant`,
   `hgcdMatrix_zero_row_invariant`, `hgcdMatrix_small_row_invariant`.
   PART XI.
8. **Pattern-det correlation + threshold entry bound** ✅
   (S15, PR #16994): `lehmerCofactors_pattern_det_correlated_from`,
   `hgcdMatrix_small_pattern_det_correlated`,
   `entry_bound_of_pattern_det_natAbs`,
   `hgcdMatrix_small_entry_bound`. PART XII.
9. **All-fuel pattern-det invariant + entry bound** ✅
   (S16, PR #17009): `cofactor_mul_pattern_det_correlated`,
   `hgcdMatrix_pattern_det_correlated`,
   `hgcdMatrixOf_pattern_det_correlated`,
   `hgcdMatrix_entry_bound`. PART XIII.
10. **Counterexample to all-fuel row-vector invariant** ✅
    (S17, PR #17024): `hgcdMatrix_130_89_value`,
    `hgcdMatrix_130_89_row_alpha`,
    `hgcdMatrix_130_89_row_beta`,
    `hgcdMatrix_row_alpha_exceeds_max`,
    `hgcdMatrix_row_beta_negative`,
    `hgcdMatrix_row_invariant_counterexample`. PART XIV. The
    proposed Session 17+ target is FALSE under the current algorithm.
11. **Path A foundation** ✅ (S18, PR #17042):
    `hgcdMatrixSafe`, `hgcdMatrixSafeOf`, `hgcdMatrixSafe_det_unit`,
    `hgcdMatrixSafe_preserves_gcd`,
    `hgcdMatrixSafeOf_det_unit`,
    `hgcdMatrixSafeOf_preserves_gcd`. New file
    `BinaryGcdOQ03OQ02PathA.lean`. Algorithm refinement with
    runtime size-reduction guard.
12. **Path A verified GCD function** ✅ (S19, this session):
    `hgcdSafeApply`, `hgcdSafeApply_gcd_eq`, `hgcdSafeGcd`,
    `hgcdSafeGcd_eq_gcd`. Computational examples on the S17
    counterexample family `(130, 89)` and worst-case `(107, 85)`.
    PART VI–VII of `BinaryGcdOQ03OQ02PathA.lean`.

**Open / Refuted**:
- **Recursive case of `hgcdMatrix_row_output_le`** ❌ (line 1078,
  sole sorry in `BinaryGcdOQ03OQ02.lean`): refuted by S17 PART XIV
  for the unguarded algorithm. Will not be closed; the path forward
  is via Path A's `hgcdMatrixSafe` (now in `…PathA.lean`), where
  size reduction holds by the runtime guard rather than by an
  algebraic lift.

Concurrently: bit-complexity claim O(M(n)·log n) remains genuinely
blocked on Mathlib (no fast multiplication, no bit-complexity model).

## Active Approach

**Path A** (S18+ chosen direction). The algorithm `hgcdMatrixSafe`
with a runtime size-reduction guard is the new implementation
target. Operational correctness is now complete: S18 proved
`hgcdMatrixSafe` is unimodular and preserves GCD; S19 wraps these
into a total correct GCD function `hgcdSafeGcd` with theorem
`hgcdSafeGcd a b = Nat.gcd a b`.

Remaining work for Path A:
- (S20) Positive size-reduction: when guard fires (compose branch),
  the column output strictly reduces.
- (S21+) Iterate to obtain a recursive GCD with HGCD-style structure.

## Blockers

* **Bit complexity (C)**: genuinely blocked on Mathlib infrastructure.
  Documented in `BinaryGcdOQ03OQ02.lean` PART VII; not a blocker on
  Path A correctness or size reduction.

* **Row-vector invariant for unguarded `hgcdMatrix`** ❌ FALSE under
  the unguarded algorithm: refuted by S17 PART XIV. This sorry on
  line 1078 will not be closed; Path A supersedes the row-vector
  approach.

## Next Action

1. **Session 20 — positive size-reduction for compose branch**:
   prove that when `hgcdMatrixSafe`'s runtime guard fires, the
   resulting matrix's column output strictly reduces `max a b`.
2. **Session 21+ — iterative HGCD-based GCD**: define a recursive
   GCD function that iterates `hgcdMatrixSafe` until below threshold,
   then dispatches to `Nat.gcd` for the base case.
3. **Bit-complexity bound**: still blocked on Mathlib; defer.

## Attempt Counts

- Total attempts: 19 (Sessions 1–19)
- Approaches tried:
  - Path A (fuel-indexed correctness): merged Session 2 (#14389)
  - Row-convention size-reduction infrastructure: Sessions 3–16
    proven correct as building blocks; the all-fuel row-vector
    invariant target was REFUTED by Session 17.
  - Path A algorithm refinement (S18, S19): GCD-preservation
    foundation laid (S18), verified GCD function (S19, this PR).
  - Path A size reduction (S20+): not yet started.
