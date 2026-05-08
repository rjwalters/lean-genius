# Current State

**Phase**: ACT
**Since**: 2026-05-01
**Iteration**: 15

## Current Focus

Pursuing the **size-reduction lemma** `hgcdMatrix_row_output_le` (PART IX,
1 sorry: recursive case for fuel ≥ 1, max a b ≥ hgcdThreshold). The proof
plan has been refactored over Sessions 12–14 to a joint induction tracking
row-output bound + entry bound simultaneously (Stehlé–Zimmermann 2004 §4).

Status of the proof plan (Sessions 1–15):

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
8. **Pattern-det coupling for HGCD** ✅ (S15, this session):
   `hgcdMatrix_pattern_det_coupled` — the conjoint invariant
   `(EvenPattern ∧ det = 1) ∨ (OddPattern ∧ det = -1)` for every HGCD
   matrix. Eliminates the spurious (Even ∧ -1) and (Odd ∧ +1) cases
   that would otherwise force a four-way split when applying
   `entry_bound_of_even` / `entry_bound_of_odd`. PART XII.

**Open**:
- **Step 4 (entry bound for HGCD)** ⏳: combine PART X (pattern) +
  PART XI (row-invariant) + PART XII (pattern-det coupling) +
  `row_vec_cramer` + `hgcdMatrix_det_unit` to derive
  `hgcdMatrix_entry_bound`. Threshold case is now derivable from the
  PART XI/XII components plus `entry_bound_of_even/odd`; recursive
  case remains.
- **Recursive case of `hgcdMatrix_row_output_le`** ⏳: the documented
  joint-induction obstacle. Resolves once `hgcdMatrix_entry_bound` is
  available for the recursive case.

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
* `hgcdMatrix_pattern_det_coupled` (S15, PART XII): the pattern-det
  coupling that lets `entry_bound_of_even/odd` apply directly.

The remaining work for Step 4 is to lift the row-vector invariant to
the recursive case via joint induction with the entry-bound side.

## Blockers

* **Pre-existing API drift in BinaryGcdOQ03OQ02.lean**: resolved by
  PR #16944 (mechanic fix for issue #16938) — `Int.natAbs_ofNat`
  rename and `split at hstep` replacement applied. File now builds
  against current Lean/Mathlib (not re-verified locally this session).

* **Bit complexity (C)**: genuinely blocked on Mathlib infrastructure.
  Documented in `BinaryGcdOQ03OQ02.lean` PART VII; not a blocker on
  (A) correctness or (B) size reduction.

## Next Action

1. **Session 16**: combine PART XI (`hgcdMatrix_small_row_invariant`)
   + PART XII (`hgcdMatrix_pattern_det_coupled`) + `row_vec_cramer` +
   `entry_bound_of_even/odd` to prove the threshold case of
   `hgcdMatrix_entry_bound`. With the pattern-det coupling, only one
   branch of the four-way split remains in each pattern case; the
   positivity-of-witnesses precondition is the main remaining
   subtlety (witnesses can be 0 if input has gcd reached zero
   coordinate).
2. **Session 17+**: tackle the recursive-case obstruction via joint
   induction, using `cofactor_mul_row_invariant` (PART XI) +
   `cofactor_mul_pattern_det_coupled` (PART XII) to chain ghost pairs
   once the IH's row-invariant at full-precision (a, b) is established
   for the inner matrix.

## Attempt Counts

- Total attempts: 15 (Sessions 1–15)
- Approaches tried:
  - Path A (fuel-indexed correctness): merged Session 2 (#14389)
  - Row-convention size-reduction infrastructure: in progress
    (Sessions 3–15 add Steps 1, 2a, 2b, 3, plus row-output composition,
    pattern lifting, row-vector base/threshold/composition law, and
    pattern-det coupling)
