# Current State

**Phase**: ACT
**Since**: 2026-05-01
**Iteration**: 14

## Current Focus

Pursuing the **size-reduction lemma** `hgcdMatrix_row_output_le` (PART IX,
1 sorry: recursive case for fuel ≥ 1, max a b ≥ hgcdThreshold). The proof
plan has been refactored over Sessions 12–14 to a joint induction tracking
row-output bound + entry bound simultaneously (Stehlé–Zimmermann 2004 §4).

Status of the proof plan (Sessions 1–14):

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
   (S14, this session): `cofactor_mul_row_invariant`,
   `hgcdMatrix_zero_row_invariant`, `hgcdMatrix_small_row_invariant`.
   PART XI.

**Open**:
- **Step 4 (entry bound for HGCD)** ⏳: combine PART X (pattern) +
  PART XI (row-invariant) + `row_vec_cramer` + `hgcdMatrix_det_unit`
  to derive `hgcdMatrix_entry_bound`. Threshold case is now
  derivable; recursive case remains.
- **Recursive case of `hgcdMatrix_row_output_le`** ⏳: the
  documented joint-induction obstacle. Resolves once
  `hgcdMatrix_entry_bound` is available for the recursive case.

Concurrently: bit-complexity claim O(M(n)·log n) remains genuinely
blocked on Mathlib (no fast multiplication, no bit-complexity model).

## Active Approach

**Joint-induction approach to size reduction** (Stehlé–Zimmermann 2004 §4
template), with the row-vector invariant for the cofactor matrix
contributed leaf-by-leaf via:

* `cofactor_mul_row_invariant` (S14, PART XI): the algebraic
  composition law.
* `hgcdMatrix_zero_row_invariant`/`hgcdMatrix_small_row_invariant`
  (S14, PART XI): the leaf cases producing natural-number residue
  witnesses, suitable for Cramer-based entry bounds.

The remaining work for Step 4 is to lift the row-vector invariant to
the recursive case via joint induction with the entry-bound side.

## Blockers

* **Pre-existing API drift in BinaryGcdOQ03OQ02.lean** (discovered S14):
  Docker build surfaced `Int.natAbs_ofNat` (3 sites) and `split at hstep`
  (3 sites) errors in code merged via PRs #14522/#14881/#14910 (Sessions
  3–7). These were merged via the deployer auto-merge path without
  successful builds (S13's docstring records the build timeouts). My
  S14 contribution elaborates cleanly in isolation; the file-level
  build is blocked on these drift issues. Should be addressed by
  mechanic/auditor (out of S14 scope).

* **Bit complexity (C)**: genuinely blocked on Mathlib infrastructure.
  Documented in `BinaryGcdOQ03OQ02.lean` PART VII; not a blocker on
  (A) correctness or (B) size reduction.

## Next Action

1. **Mechanic/auditor**: fix `Int.natAbs_ofNat` rename and `split at hstep`
   replacement in PARTS V.5/VI/IX of `BinaryGcdOQ03OQ02.lean` so the
   file builds end-to-end.
2. **Session 15**: derive `hgcdMatrix_entry_bound` for the threshold
   case using PART X (pattern) + PART XI (row-invariant) +
   `row_vec_cramer` + `hgcdMatrix_det_unit`.
3. **Session 16+**: tackle the recursive-case obstruction via joint
   induction, using `cofactor_mul_row_invariant` (PART XI) to chain
   ghost pairs once the IH's row-invariant at full-precision (a, b) is
   established for the inner matrix.

## Attempt Counts

- Total attempts: 14 (Sessions 1–14)
- Approaches tried:
  - Path A (fuel-indexed correctness): merged Session 2 (#14389)
  - Row-convention size-reduction infrastructure: in progress
    (Sessions 3–14 add Steps 1, 2a, 2b, 3, plus row-output composition,
    pattern lifting, and row-vector base/threshold/composition law)
