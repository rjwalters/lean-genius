# Current State

**Phase**: REFLECT — Session 17 surfaced a foundational counterexample;
the Session 17+ target stated in S16 was IMPOSSIBLE. The proof program
now needs an architectural redirect (algorithm refinement, restricted
target, or column-convention strategy).

**Since**: 2026-05-01
**Iteration**: 17

## Current Focus

PART XIV (Session 17, this session) introduces a `native_decide`-checked
**counterexample** to the proposed all-fuel row-vector invariant.

The decided witness is at `(a, b) = (130, 89)` and `fuel = 5`:
  * `hgcdMatrix 5 130 89 = ⟨-3, 5, 20, -33⟩` (det = -1, OddPattern).
  * Row output at the input pair: `(1390, -2287)`.
  * α-row magnitude `1390 > 2 · max 130 89 = 260`, AND β-row product
    `-2287 < 0` (no natural-number witness possible).

This refutes both the Session 17+ target `hgcdMatrix_row_invariant`
and (as a corollary) the recursive case of `hgcdMatrix_row_output_le`
(line 1078). A computational survey on `(a, b) ∈ [64, 130) × [64, a]`
finds 875/2211 ≈ 39.6% of pairs above threshold violate the row-output
bound, with the worst case `(107, 85)` producing matrix entries on
the order of `10^268` — catastrophic non-reduction. The Schönhage HGCD
**as currently formalized** does not size-reduce on a substantial
fraction of inputs above threshold.

PARTS XI–XIII (Sessions 14–16) remain mathematically valid: their
theorems are unconditional truths, and `hgcdMatrix_entry_bound`
(PART XIII) is correctly stated as conditional on row-vector
witnesses — witnesses which this counterexample shows do not exist
for general recursive inputs.

Status of the proof plan (Sessions 1–17):

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
   (S16): `cofactor_mul_pattern_det_correlated`,
   `hgcdMatrix_pattern_det_correlated`,
   `hgcdMatrixOf_pattern_det_correlated`,
   `hgcdMatrix_entry_bound`. PART XIII.
10. **Counterexample to all-fuel row-vector invariant** ✅
    (S17, this session): `hgcdMatrix_130_89_value`,
    `hgcdMatrix_130_89_row_alpha`,
    `hgcdMatrix_130_89_row_beta`,
    `hgcdMatrix_row_alpha_exceeds_max`,
    `hgcdMatrix_row_beta_negative`,
    `hgcdMatrix_row_invariant_counterexample`. PART XIV. The
    proposed Session 17+ target is FALSE under the current algorithm.

**Open / Refuted**:
- **Recursive case of `hgcdMatrix_row_output_le`** ❌ (line 1078,
  sole remaining sorry): the statement is FALSE for `(a, b) =
  (130, 89)`, where the α-row magnitude is `1390 > 130`. The
  `sorry` cannot be discharged with the current algorithm
  definition. Path forward (A/B/C) detailed below.

Concurrently: bit-complexity claim O(M(n)·log n) remains genuinely
blocked on Mathlib (no fast multiplication, no bit-complexity model).

## Active Approach

**Three candidate paths** (Session 18+ requires choosing one):

**(A) Algorithm refinement.** Modify `hgcdMatrix` to add a
size-reduction safety check: after computing `(u, v) =
(M_inner.apply (a, b)).natAbs`, abort the recursive branch (return
`M_inner` alone, or fall back to direct Lehmer accumulation) when
`max u v ≥ max a b`. This matches GMP's `mpn_hgcd` and similar
production HGCD implementations. Cost: re-prove `hgcdMatrix_det_unit`,
`hgcdMatrix_preserves_gcd`, and the threshold infrastructure for the
new definition. The row-vector invariant should then hold by
construction (the safety check enforces residue monotonicity).

**(B) Restricted size-reduction theorem.** Reformulate the size
reduction to apply only on a "well-behaved" subset (e.g., Fibonacci-
like quotient sequences where the algorithm naturally reduces).
Document the restriction explicitly in the theorem hypotheses. Cost:
formalize the "well-behaved" predicate; show how representative the
restricted class is for cryptographic-sized inputs.

**(C) Column-convention strategy.** Pursue size reduction directly
via the column action `M.apply (a, b)`, sidestepping the row-vector
invariant. The natural inductive structure
`(M_outer.mul M_inner).apply (a, b) = M_outer.apply (M_inner.apply (a, b))`
matches the algorithm's own dataflow: M_outer's natural inputs ARE
the column-output of M_inner. Cost: re-derive entry bounds in column
convention; the existing PART VI/VII infrastructure largely transfers.

## Blockers

* **Bit complexity (C)**: genuinely blocked on Mathlib infrastructure.
  Documented in `BinaryGcdOQ03OQ02.lean` PART VII; not a blocker on
  (A) correctness or (B) size reduction.

* **Row-vector invariant** ❌ FALSE under current algorithm: refuted
  by S17 PART XIV `hgcdMatrix_row_invariant_counterexample`. Cannot
  be proved without changing the algorithm or restricting the input.

## Next Action

1. **Session 18 — choice of path**: select among (A) algorithm
   refinement, (B) restricted theorem, or (C) column-convention.
   Recommendation: **(C) column-convention** is the cleanest given
   that S15-S16 entry bounds already use natAbs; and the
   `cofactor_mul_apply` chaining naturally handles the M_outer/M_inner
   composition with M_outer's IH at its own inputs (u, v).
2. **Session 19+ — execute selected path**: develop the column-
   convention size-reduction proof (or the algorithm refinement, if
   (A) is chosen).
3. **Bit-complexity bound**: still blocked on Mathlib; defer.

## Attempt Counts

- Total attempts: 17 (Sessions 1–17)
- Approaches tried:
  - Path A (fuel-indexed correctness): merged Session 2 (#14389)
  - Row-convention size-reduction infrastructure: Sessions 3–16
    proven correct as building blocks; the all-fuel row-vector
    invariant target was REFUTED by Session 17.
  - Path forward (after S17 redirect): one of (A)/(B)/(C) above.
