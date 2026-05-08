# Current State

**Phase**: ACT
**Since**: 2026-05-01
**Iteration**: 16

## Current Focus

Pursuing the **size-reduction lemma** `hgcdMatrix_row_output_le`
(PART IX, 1 sorry: recursive case for fuel ≥ 1, max a b ≥ hgcdThreshold).
The Stehlé–Zimmermann 2004 §4 joint induction is no longer coupled
across pattern-det × row-vector — Session 16 (PART XIII) closes the
pattern-det side for all fuel by plain induction, leaving only the
row-vector invariant as the remaining circular ingredient.

Status of the proof plan (Sessions 1–16):

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
   (S16, this session): `cofactor_mul_pattern_det_correlated`,
   `hgcdMatrix_pattern_det_correlated`,
   `hgcdMatrixOf_pattern_det_correlated`,
   `hgcdMatrix_entry_bound`. PART XIII.

**Open**:
- **Recursive case of `hgcdMatrix_row_output_le`** ⏳ (line 1078,
  sole remaining sorry): single-axis joint induction on the
  row-vector invariant for `hgcdMatrix` at arbitrary fuel.
  Pre-S16 the joint induction was coupled (entry-bound side needed
  the row-vector side, which needed the entry-bound side). Post-S16
  the entry bound is available for all fuel as a black box
  (`hgcdMatrix_entry_bound`, PART XIII), so the joint induction
  reduces to the row-vector axis alone.

Concurrently: bit-complexity claim O(M(n)·log n) remains genuinely
blocked on Mathlib (no fast multiplication, no bit-complexity model).

## Active Approach

**Single-axis joint induction** (post-S16): with
`hgcdMatrix_entry_bound` (PART XIII) as a black-box ingredient,
simultaneously prove
- (RO) row-output bound: `(a · M.α + b · M.γ).natAbs ≤ max a b` for
  `M = hgcdMatrix fuel a b`, on the algorithm's own inputs.
- (RV) row-vector existential: `∃ ahat' bhat',
  (a, b) · M = (ahat', bhat')` with the residue-monotonicity bound.

Both at the same fuel and same inputs, by induction on fuel. The
recursive case uses `cofactor_mul_row_invariant` (PART XI) to chain
through `M_outer.mul M_inner`, with `hgcdMatrix_entry_bound`
(PART XIII) supplying the entry bounds for both factors.

## Blockers

* **Bit complexity (C)**: genuinely blocked on Mathlib infrastructure.
  Documented in `BinaryGcdOQ03OQ02.lean` PART VII; not a blocker on
  (A) correctness or (B) size reduction.

* **Recursive row-vector invariant**: residual obstacle. Pre-S16
  required coupled joint induction; post-S16 reduces to single-axis
  joint induction with all other ingredients as black boxes.

## Next Action

1. **Session 17+**: prove `hgcdMatrix_row_invariant` (existential
   row-vector invariant for arbitrary fuel) via single-axis joint
   induction. Use `hgcdMatrix_entry_bound` (S16) as black-box entry
   bound, `cofactor_mul_row_invariant` (S14) to chain, and
   `cofactor_mul_row_output_natAbs_le` (S12) for the row-output
   side of the joint statement.
2. **Session 18+**: close the recursive case of
   `hgcdMatrix_row_output_le` (line 1078) using the row-vector
   invariant from S17 and the existing infrastructure.
3. **Session 19+**: derive `hgcdMatrix_full_entry_bound` (no
   row-vector witnesses required) by combining `hgcdMatrix_entry_bound`
   (S16) with the unconditional `hgcdMatrix_row_invariant` (S17).

## Attempt Counts

- Total attempts: 16 (Sessions 1–16)
- Approaches tried:
  - Path A (fuel-indexed correctness): merged Session 2 (#14389)
  - Row-convention size-reduction infrastructure: ongoing
    (Sessions 3–16 add Steps 1, 2a, 2b, 3, row-output composition,
    pattern lifting, row-vector base/threshold/composition law,
    pattern-det correlation + threshold entry bound, and the
    Session 16 all-fuel pattern-det + entry-bound lift)
