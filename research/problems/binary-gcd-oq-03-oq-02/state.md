# Current State

**Phase**: ACT — Path A's algorithmic story (S18–S20), primary
API (S21–S22), the outer-guard branching characterisation (S23),
and now the survey-range tabulation framework for outer-guard
density (S24) are in place. S24 (this session) adds
`surveyRange : List (ℕ × ℕ)` (the explicit 2211-pair lower
triangle on `[64, 130) × [64, 130)`), proves
`surveyRange.length = 2211` via `native_decide`, and defines
`outerGuardFiresInSurveyRange` / `outerGuardAbortsInSurveyRange`
counting functions. The exact density magnitude is left for
future `native_decide` evaluation; this session establishes the
framework and confirms enumeration size.

**Since**: 2026-05-01
**Iteration**: 24

## Current Focus

Session 24 (this PR, researcher-6) adds the **survey-range
tabulation framework** (Path A PART XV) for measuring outer-guard
density on the S17 PART XIV counterexample family. Three
contributions:

  - `surveyRange : List (ℕ × ℕ)` — explicit lower-triangular
    enumeration of `{(a, b) : 64 ≤ b ≤ a < 130}`, built via
    nested `foldr` / `::` (no `bind`/`flatMap` dependency).
  - `surveyRange_length : surveyRange.length = 2211` — confirms
    the enumeration covers `66 · 67 / 2` pairs. By
    `native_decide` on a structural fold over `List.range`,
    independent of any HGCD recursion (fast).
  - `outerGuardFiresInSurveyRange` and
    `outerGuardAbortsInSurveyRange` — `ℕ`-valued count
    definitions partitioning the survey range by
    `schonhageOuterGuardFires`. Future sessions can plug
    `native_decide` evaluations on these counts to obtain the
    exact density magnitude.

Net: +59 lines (1 theorem + 3 defs), 0 new axioms, 0 new sorries.
Together with S23's headline theorem
`schonhageGcd_succ_via_outerGuard`, the outer-guard story is now
both qualitatively (S23) and structurally (S24) anchored: the
QUALITATIVE branching is fully described by a Boolean predicate
and the QUANTITATIVE density framework is in place to support
future `native_decide` magnitude measurements.

Session 23 introduced an outer-guard predicate
characterisation of `schonhageGcd`'s recursive case. The predicate
`schonhageOuterGuardFires : ℕ → ℕ → Bool` returns `true` iff
applying `hgcdSafeApply a b` strictly reduces `max a b` (and the
input is above threshold). Five structural lemmas provide the
core reduction equations:

  - `schonhageOuterGuardFires_below_threshold` — uniformly false
    on small inputs.
  - `schonhageOuterGuardFires_iff` — conjunctive iff with
    above-threshold AND strict-decrease.
  - `schonhageOuterGuardFires_strict_decrease` — forward direction:
    the firing guard implies strict size-reduction at the next step.
  - `schonhageGcd_succ_via_outerGuard` — **headline theorem**: one
    fuel step of `schonhageGcd` is fully described by the predicate
    (recurse if fires, dispatch to `Nat.gcd` if aborts).
  - Specialisations: `_recurse_of_fires` and `_fallback_of_aborts`.

Five `native_decide`-checked below-threshold witnesses confirm
the closed-form Boolean kernel agrees with the abstract
characterisation on concrete sub-threshold inputs.

Session 22 extended the S21 API surface with six further `Nat.gcd`
identities not previously packaged (`schonhageGcdOf_dvd_iff`,
`_mul_left`, `_mul_right`, `_pos_of_pos_left`,
`_pos_of_pos_right`, `_succ_self`) and added a PART XII section of
five `native_decide`-checked sanity examples. Together with S21
the algebraic API for `schonhageGcdOf` now mirrors the standard
Mathlib `Nat.gcd` theory, and the `native_decide` checks confirm
the closed-form recursion produces correct answers on inputs
where the unguarded `hgcdMatrix` (S17) blew up.

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
    PR #17087): `schonhageGcd`, `schonhageGcdOf`,
    `schonhageGcd_zero`, `schonhageGcd_succ`,
    `hgcdSafeApply_natAbs_gcd`, `schonhageGcd_eq_gcd`,
    `schonhageGcdOf_eq_gcd`. PART VIII–IX of
    `BinaryGcdOQ03OQ02PathA.lean`. Total correct iterated GCD
    with two structural fallbacks (below-threshold + per-step
    guard). Native-decide examples include the S17
    counterexample family and `(1000000, 999999)`.
14. **API surface for `schonhageGcdOf`** ✅ (S21, PR #17104):
    11 wrapper lemmas covering the standard `Nat.gcd` identities
    (`schonhageGcdOf_zero_left`, `_zero_right`, `_self`,
    `_one_left`, `_one_right`, `_comm`, `_dvd_left`, `_dvd_right`,
    `dvd_schonhageGcdOf`, `_assoc`, `_eq_zero_iff`) plus
    `schonhageGcd_fuel_irrelevant`. PART X of
    `BinaryGcdOQ03OQ02PathA.lean`. Each wrapper reduces to
    `schonhageGcdOf_eq_gcd` plus the corresponding `Nat.gcd`
    lemma. The lemmas are uniformly trivial; their value is
    pragmatic — `schonhageGcdOf` now responds to standard
    `simp`-style tactics without manual unfolding at the call
    site, completing the drop-in replacement story.
15. **Extended algebraic identities + empirical witnesses** ✅
    (S22, PR #15091): 6 additional wrapper lemmas in PART XI
    (`schonhageGcdOf_dvd_iff`, `_mul_left`, `_mul_right`,
    `_pos_of_pos_left`, `_pos_of_pos_right`, `_succ_self`) plus 5
    PART XII `native_decide` empirical sanity examples
    (`(64, 64)`, `(65, 64)`, `(121, 88)`, `(200, 175)`,
    `(2520, 1980)`). The S22 wrappers fill the gaps left by S21:
    multiplicative laws, the iff form of the universal property,
    strict positivity from either side, and a concrete Fibonacci-
    style coprimality witness. The PART XII examples exercise the
    closed-form recursion at scale — the kernel reduces every fuel
    level and every `hgcdSafeApply` call.
16. **Outer-guard predicate + branching characterisation** ✅
    (S23, this session): Boolean predicate
    `schonhageOuterGuardFires : ℕ → ℕ → Bool` capturing the OUTER
    size-reduction guard from `schonhageGcd`'s recursive case
    (PART VIII line 440), plus five structural lemmas in PART
    XIII (`_below_threshold`, `_iff`, `_strict_decrease`,
    `schonhageGcd_succ_via_outerGuard` — the headline reduction
    equation, and the two specialisations `_recurse_of_fires` /
    `_fallback_of_aborts`). PART XIV adds five
    `native_decide`-checked below-threshold witnesses
    (`(0, 0)`, `(5, 3)`, `(12, 8)`, `(63, 1)`, `(63, 63)`),
    confirming the predicate is uniformly `false` on small inputs.
    The headline theorem reduces every reasoning step about the
    `schonhageGcd` recursion to a Boolean case-split on the
    predicate, factoring out the algebra of the threshold check
    + size-reduction guard. This is the qualitative foundation
    for S24+ density theorems.

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
- S21: API surface (PART X) — eleven wrapper lemmas + fuel
  irrelevance, making `schonhageGcdOf` a drop-in replacement
  for `Nat.gcd` under standard rewriting tactics.
- S22: extended algebraic identities (PART XI) and empirical
  witnesses (PART XII) — six further wrappers covering the gaps
  in S21 plus five `native_decide` sanity examples spanning the
  threshold edge and the S17 survey range.

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

1. **Session 25 — outer-guard density magnitude**: with the S24
   tabulation framework in place, run `native_decide` on
   `outerGuardFiresInSurveyRange` and
   `outerGuardAbortsInSurveyRange` to obtain the exact density
   numbers. Likely 60–120 seconds of native_decide compute time
   per count (2211 calls × ~ ms-scale `hgcdSafeApply` evaluation).
   Once magnitudes are known, package them as named constants
   (`schonhageOuterGuard_fires_count`,
   `schonhageOuterGuard_aborts_count`) and add a `decide`-checked
   sum-equals-2211 partition theorem. The relative magnitude
   answers the qualitative-vs-quantitative gap left by S17 PART
   XIV: if firing density is high (e.g. > 80%), Schönhage gives a
   measurable speedup on this regime; if low, fallback dominates.
2. **Session 26+ — inner-reduction characterisation**: refine the
   *inner* runtime guard analysis for `hgcdMatrixSafe` itself,
   complementing the S23 outer-guard predicate. This is the
   second-level question the S17 PART XIV counterexample raised.
3. **Coprime-bit-length theorem**: with the S24 framework, the
   stronger sub-target — "every coprime pair above threshold with
   matching bit-length triggers the outer guard" — becomes a
   *theorem candidate* whose statement is now well-typed in the
   PathA file. Proving it requires structural analysis of
   `hgcdSafeApply`, deferred.
4. **Bit-complexity bound**: still blocked on Mathlib; defer.
5. **Mathlib upstream**: the current `schonhageGcdOf` API surface
   (S21+S22) is now sufficient that, contingent on a working
   Docker build, candidate Mathlib upstream PRs could be drafted
   for one or two of the routine wrapper lemmas. Survey what
   already exists in Mathlib's `Nat.GCD` family before submitting.

## Attempt Counts

- Total attempts: 23 (Sessions 1–23)
- Approaches tried:
  - Path A (fuel-indexed correctness): merged Session 2 (#14389)
  - Row-convention size-reduction infrastructure: Sessions 3–16
    proven correct as building blocks; the all-fuel row-vector
    invariant target was REFUTED by Session 17.
  - Path A algorithm refinement: GCD-preservation foundation
    (S18, #17042), verified single-step GCD function (S19, #17063),
    recursive Schönhage-style iterated GCD (S20, #17087).
  - Path A API surface (S21, #17104): standard `Nat.gcd` API
    transferred to `schonhageGcdOf`; fuel irrelevance packaged.
  - Path A extended algebraic identities + empirical witnesses
    (S22, #15091): multiplicative laws, dvd-iff, positivity,
    coprimality witness, plus 5 `native_decide` sanity examples.
  - Path A outer-guard branching characterisation (S23, this PR):
    Boolean predicate + 5 structural lemmas + 5 below-threshold
    `native_decide` witnesses. Headline reduction equation
    `schonhageGcd_succ_via_outerGuard` reduces every reasoning
    step about the recursion to a Boolean case-split.
  - Path A quantitative bounds (S24+): pending.
