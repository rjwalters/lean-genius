# Current State

**Phase**: ACT — Path A chosen post-S17. S20 closes the verified
ALGORITHMIC story for Path A: `schonhageGcd` is a recursive
Schönhage-style GCD function with correctness
`schonhageGcd a b = Nat.gcd a b`, total and 0 axioms.

**Since**: 2026-05-01
**Iteration**: 20

## Current Focus

Session 20 builds on S18–S19 to define an ITERATIVE Schönhage-style
GCD function `schonhageGcd : ℕ → ℕ → ℕ → ℕ` (and top-level
`schonhageGcdOf`), with correctness theorem
`schonhageGcd_eq_gcd : schonhageGcd fuel a b = Nat.gcd a b` for
every fuel and every pair of natural inputs.

The body iterates `hgcdSafeApply` (S19) on the reduced pair: each
step takes the column output `(p.1.natAbs, p.2.natAbs)` and
recurses ONLY if its `max` is strictly less than `max a b`.
Otherwise — and on inputs below threshold — the function falls
back to `Nat.gcd`. With these two structural fallbacks, the
function is total and unconditionally correct: even on
pathological inputs like the S17 counterexample family
`(130, 89)`, where `hgcdMatrixSafe`'s OWN inner guard always
aborts, the OUTER guard here dispatches to `Nat.gcd` and the
correctness theorem still holds.

This is the verified ENDPOINT of Path A's algorithmic story:
- Single-step correctness: S19's `hgcdSafeGcd_eq_gcd`.
- Iterative correctness: S20's `schonhageGcd_eq_gcd`.

The remaining work (S21+) is QUANTITATIVE — establishing that the
runtime guards fire often enough that the recursion outperforms
plain `Nat.gcd` asymptotically.

Path A roadmap remaining (S21+):

1. **S21 — quantitative inner-reduction characterisation**: prove
   that the inner runtime guard of `hgcdMatrixSafe` fires for a
   well-defined density of inputs above threshold. The S17 PART
   XIV counterexample shows the guard CAN abort, but in survey
   ranges the guard fires often; quantifying the success rate
   would yield a probabilistic speedup bound.

2. **Bit-complexity bound** (`O(M(n)·log n)`): genuinely blocked
   on Mathlib (no fast multiplication, no bit-complexity model).
   Documented; defer until Mathlib lands these.

3. **Empirical comparison**: native_decide-checked timing /
   instruction count comparison of `schonhageGcdOf` vs `Nat.gcd`
   on the S17 counterexample family.

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
12. **Path A verified GCD function** ✅ (S19, PR #17063):
    `hgcdSafeApply`, `hgcdSafeApply_gcd_eq`, `hgcdSafeGcd`,
    `hgcdSafeGcd_eq_gcd`. Computational examples on the S17
    counterexample family `(130, 89)` and worst-case `(107, 85)`.
    PART VI–VII of `BinaryGcdOQ03OQ02PathA.lean`.
13. **Recursive Schönhage-style GCD via iteration** ✅ (S20,
    this session): `schonhageGcd`, `schonhageGcdOf`,
    `schonhageGcd_zero`, `schonhageGcd_succ`,
    `hgcdSafeApply_natAbs_gcd`, `schonhageGcd_eq_gcd`,
    `schonhageGcdOf_eq_gcd`. PART VIII–IX of
    `BinaryGcdOQ03OQ02PathA.lean`. Total correct iterated GCD
    with two structural fallbacks (below-threshold + per-step
    guard). Native-decide examples include the S17
    counterexample family and `(1000000, 999999)`.

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
with a runtime size-reduction guard is the implementation target.
The verified ALGORITHMIC story for Path A is now complete:

- S18: `hgcdMatrixSafe` is unimodular (`hgcdMatrixSafe_det_unit`)
  and preserves GCD (`hgcdMatrixSafe_preserves_gcd`).
- S19: a single-step GCD function `hgcdSafeGcd` wraps that
  matrix application; correct via `hgcdSafeGcd_eq_gcd`.
- S20: a recursive iterated GCD function `schonhageGcd` with
  guarded fallback to `Nat.gcd`; correct via
  `schonhageGcd_eq_gcd`. Total and unconditional.

Remaining work for Path A is QUANTITATIVE only (asymptotic
speedup, bit-complexity bound).

## Blockers

* **Bit complexity (C)**: genuinely blocked on Mathlib infrastructure.
  Documented in `BinaryGcdOQ03OQ02.lean` PART VII; not a blocker on
  Path A correctness or size reduction.

* **Row-vector invariant for unguarded `hgcdMatrix`** ❌ FALSE under
  the unguarded algorithm: refuted by S17 PART XIV. This sorry on
  line 1078 will not be closed; Path A supersedes the row-vector
  approach.

## Next Action

1. **Session 21 — quantitative inner-reduction characterisation**:
   establish the input regime in which `hgcdMatrixSafe`'s inner
   runtime guard fires. The S17 PART XIV counterexample shows the
   guard can abort, but a density argument may still yield a
   probabilistic speedup bound.
2. **Empirical comparison**: native_decide-checked
   `schonhageGcdOf` on the S17 counterexample family vs `Nat.gcd`,
   to characterise the practical impact of the OUTER guard
   firing on those inputs.
3. **Bit-complexity bound**: still blocked on Mathlib; defer.

## Attempt Counts

- Total attempts: 20 (Sessions 1–20)
- Approaches tried:
  - Path A (fuel-indexed correctness): merged Session 2 (#14389)
  - Row-convention size-reduction infrastructure: Sessions 3–16
    proven correct as building blocks; the all-fuel row-vector
    invariant target was REFUTED by Session 17.
  - Path A algorithm refinement: GCD-preservation foundation
    (S18, #17042), verified single-step GCD function (S19, #17063),
    recursive Schönhage-style iterated GCD (S20, this PR).
  - Path A quantitative bounds (S21+): pending.
