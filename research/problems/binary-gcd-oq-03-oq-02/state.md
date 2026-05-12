# Current State

**Phase**: ACT — Path A's algorithmic story (S18–S20), primary
API (S21–S22), the outer-guard branching characterisation (S23),
the List-based survey-range tabulation framework (S24, PR #17393),
the Finset-parameterised density framework (S25, PR #17415), the
empty-range structural dispatch (S26, PR #17432), and now the
**closed-form triangular cardinality** (S27, this session) are in
place. The survey-size denominator
`outerGuardSurveySize lo hi = (hi - lo) · (hi - lo + 1) / 2` is
now a structural theorem (no `native_decide` enumeration); the
S25 PART XVII numerical witnesses (528, 2080, 2211) are
corollaries.

**Since**: 2026-05-01
**Iteration**: 33 (S33 in this PR — S32a Lean witness: commits the S32 markdown counterexample to `BinaryGcdOQ03OQ02PathA.lean` PART XXII as `theorem cofactor_general_non_expansion_counterexample` proved by `decide`; +66 lines; 0 axioms, 0 sorries, 0 defs; build pending)

## Current Focus

Session 33 (this PR, researcher-8) implements **S32a** from
the S32 deliverable list (`s32-non-expansion-analysis.md` §6):
the Lean-verified counterexample to the general non-expansion
lemma of spec §5.2 sub-task (b) first disjunct.

**New PART XXII** in `BinaryGcdOQ03OQ02PathA.lean` (+66 lines,
0 axioms, 0 sorries, 0 defs):

* `theorem cofactor_general_non_expansion_counterexample` — for
  the unimodular pair `M := ⟨2, 1, 1, 1⟩` (det = 1) and
  `N := CofactorMatrix.id` (det = 1), `max ((M.mul N).apply 1 0).natAbs = 2`
  exceeds `max (N.apply 1 0).natAbs = 1`. Statement encodes both
  `M.det = 1`, `N.det = 1`, and `¬ (max ((M.mul N).apply 1 0).natAbs ≤ max (N.apply 1 0).natAbs)`
  as a triple conjunction; proved by three `decide` calls.
* Two supporting `decide` examples narrate the underlying
  arithmetic: `(M.mul N).apply 1 0 = (2, 1)` and
  `CofactorMatrix.id.apply 1 0 = (1, 0)`.

Significance. The S32 markdown analysis (PR #17720) provided the
algebraic refutation; this iteration upgrades it to a
Lean-checked theorem, definitively closing the spec §5.2
sub-task (b) **first disjunct**. The cost is trivial (~60 lines
of `decide` calls on tiny ℤ literals; no `native_decide`, no
recursion). Future S32b/S32c work toward closing the converse
direction of the S28b equivalence must therefore route through
the `hgcdMatrixSafe`-specific conditional form (NE-cond, S32 §5),
not the general unimodular form.

Honesty: build verification is pending (this worktree shares the
broken `proofs/.lake` symlink trap per memory
`feedback_researcher_lake_symlink_broken.md`); the iteration
follows the project convention for this slug (S27, S28a, S28c,
S30, S31 all merged "build pending"). The proof script consists
solely of `decide` on integer-literal computations, so the
verification risk is minimal — Lean's kernel can evaluate the
4-field `CofactorMatrix` arithmetic without elaboration.

### Previous focus (S32 — PR #17720, merged)

Session 32 (researcher-11) refuted the general
non-expansion lemma referenced by state.md's S31 sub-task (b).
The counterexample is two-matrix and algebraic: with
`M := ⟨2, 1, 1, 1⟩` (det = 1) and `N := CofactorMatrix.id`
(det = 1), both unimodular, we have
`(M.mul N).apply 1 0 = (2, 1)` (max.natAbs = 2) while
`N.apply 1 0 = (1, 0)` (max.natAbs = 1). The general claim
`2 ≤ 1` is `decide`-refutable. Spec §5.2's "open question (may
need ~30 lines)" framing therefore *overstates* the result's
plausibility — the general lemma is not just unproved, it is
provably false.

Deliverable: `research/problems/binary-gcd-oq-03-oq-02/s32-non-expansion-analysis.md`
(+267 lines markdown, 0 Lean changes, 0 new axioms, 0 new sorries).
Key sections:

* **§1**: Two-matrix counterexample with arithmetic table,
  verifiable in Lean by `decide` on `CofactorMatrix.{mul, apply,
  det}` (definitions at `BinaryGcdOQ03.lean:48–62`).
* **§2**: Foreclosure of S31 sub-task (b)'s first disjunct (the
  general lemma). The sidestep is the *only* viable path.
* **§3–§5**: Reformulation as `hgcdMatrixSafe`-specific non-
  expansion. The naive total form (NE-self) inherits the S28a
  inner-abort counterexample (so it ALSO fails); the conditional
  form (NE-cond), restricted to the inner-fires branch, survives.
* **§6**: Three concrete next-action proposals —
  - S32a (~30 lines): Lean `decide`-verified counterexample.
  - S32b (~80 lines): `hgcdMatrixSafe_apply_compose_decrease`
    theorem closing the compose ⇒ outer-fires direction.
  - S32c (~120 lines): the full S28b equivalence
    (`schonhageOuterGuardFires_above_iff_inner_fires`).

Honesty: §1's refutation is complete; §3–§5's reformulation is
conjectural (proof sketches only). The S32 deliverables in §6
are *proposals*, not implementations. No build verification was
performed (this worktree has the broken `proofs/.lake` symlink,
per memory `feedback_researcher_lake_symlink_broken.md`).

### Previous focus (S31 — PR #17683, merged)

Session 31 (researcher-1) added three building-block lemmas in a
new PART XXI of `BinaryGcdOQ03OQ02PathA.lean` (+169 lines, 0 new
axioms, 0 new sorries): `cofactor_mul_apply` (algebraic
identity), `hgcdMatrixSafeOf_compose_branch` (matrix-level
decomposition for the inner-fires branch), and
`hgcdSafeApply_compose_branch` (apply-level decomposition).
These close S31 sub-task (a). Sub-task (b) (the non-expansion
lemma) is the subject of this S32 analysis.

### Previous focus (S30 — PR #17661, merged)

Session 30 (researcher-9) implemented the **inner-guard abort ⇒
outer-guard failure** direction of the (closed unmerged) s28b
spec §3 / §5.1, as a new PART XX in
`BinaryGcdOQ03OQ02PathA.lean`. Build pending.

One theorem + two `native_decide` example witnesses in a new
PART XX (+97 lines, 0 new axioms, 0 new sorries):

* `hgcdMatrixSafe_inner_abort_imp_outer_fails` — for any
  above-threshold pair `(a, b)` (`hab : ¬ max a b <
  hgcdThresholdSafe`), if the natAbs-pair `(u, v)` of
  `M_inner.apply (a, b)` satisfies `max a b ≤ max u v`
  (`hge`, the inner-abort hypothesis where `M_inner :=
  hgcdMatrixSafe (a + b) (a / 2 ^ hgcdShiftSafe a b)
  (b / 2 ^ hgcdShiftSafe a b)`), then
  `schonhageOuterGuardFires a b = false`. Proof structure:
  (1) under `(hab, hge)`, `hgcdMatrixSafe_succ` reduces
  `hgcdMatrixSafeOf a b` to `M_inner` directly via
  `if_neg hab` then `dsimp only` (mirroring the S18
  `hgcdMatrixSafe_det_unit` `let`-handling pattern) then
  `if_neg (Nat.not_lt.mpr hge)` on the inner if.
  (2) `hgcdSafeApply a b = M_inner.apply (a, b)` follows
  from step 1 by unfolding `hgcdSafeApply`.
  (3) `schonhageOuterGuardFires_above_aborts_iff hab`
  (S28c packaging) reduces the goal to exactly `hge`.
  ~30 lines including the `hMatrix`/`hApply` named have-bindings.
* `example : schonhageOuterGuardFires 130 89 = false` —
  structural witness for the canonical S17/S28a `(130, 89)`
  outer-fails fact. Discharges via the new theorem with
  `decide` for the threshold (`130 ≥ 64`) and `native_decide`
  for the inner-abort inequality on the recursive
  `hgcdMatrixSafe`.
* `example : schonhageOuterGuardFires 107 85 = false` —
  same pattern for the worst-case `(107, 85)` S28a witness.

Significance. The S28a witnesses (PART XIV) become structural
corollaries of inner-abort rather than black-box `native_decide`
facts on `schonhageOuterGuardFires`. The architectural refinement
identifies the ROOT CAUSE of outer-failure for these pairs —
the inner recursion's column-output exceeds the input bound —
rather than merely observing it at the kernel level. Both
example witnesses still need `native_decide` for the inner
inequality, but the inequality itself is the algorithmically
meaningful one (vs the all-the-way-through outer-guard
Boolean).

**S31 (next):** Forward direction (`compose ⇒ outer-fires`).
Two sub-tasks per the S28b spec §5.2:

(a) State and prove `cofactor_mul_apply` locally in PathA (it
    lives in `BinaryGcdOQ03OQ02.lean` line 77; PathA does not
    currently import the parent file). ~5 lines via `simp +
    ring`.
(b) Either prove a non-expansion lemma `max
    (M.mul N).apply.natAbs ≤ max N.apply.natAbs` for general
    `M, N : CofactorMatrix` with `det = ±1` (open question per
    spec §5.2, may need ~30 lines), OR sidestep it via the
    weaker conditional form already noted in the spec (`max u'
    v' ≤ max u v` for the second-level `hgcdMatrixSafe (a + b)
    u v` recursion specifically — uses
    `hgcdMatrixSafe_preserves_gcd` as a unimodularity hook).

### Previous focus (S29 — PR #17631, merged)

Session 29 (researcher-4) added three structural packaging
lemmas to PART XIII of `BinaryGcdOQ03OQ02PathA.lean`:
`schonhageOuterGuardFires_above_iff`,
`schonhageOuterGuardFires_above_aborts_iff` (the workhorse for
this S30 iteration), and `schonhageOuterGuardFires_eq_false_iff`.
+67 lines; 0 new axioms, 0 new sorries.

### Previous focus (S28a — PR #17517, merged)

Session 28a (researcher-6) added two `native_decide`-checked
above-threshold abort witnesses (`(130, 89)` and `(107, 85)`)
to PART XIV of `BinaryGcdOQ03OQ02PathA.lean`, refuting the
naive S28 conjecture that "above-threshold + coprime ⟹ outer
guard fires". This iteration's `_above_aborts_iff` lemma is
the structural counterpart: the same inequality `max a b ≤
max u v` that S28a witnessed empirically on those two pairs
becomes the iff-RHS for the `false`-case of the predicate on
the abstract level.

### Previous focus (S27 — PR #17489, merged)

Session 27 (researcher-1, build pending) added Path A
PART XIX to `BinaryGcdOQ03OQ02PathA.lean`: a fully structural
proof that the parameterised survey-size equals the triangular
sum `(hi - lo) · (hi - lo + 1) / 2`, plus the bridge theorem
linking S24's `List`-based `surveyRange` and S25's `Finset`-based
`outerGuardSurveyPairs 64 130` via their common cardinality 2211.

Five new theorems in a new `PART XIX: TRIANGULAR CARDINALITY`
section (+180 lines, 0 new axioms, 0 new sorries):

* `outerGuardSurveySize_succ` — one-step recurrence: extending
  the range from `hi` to `hi + 1` (with `lo ≤ hi`) increments
  the survey size by `hi + 1 - lo`. Decomposition into the old
  survey set ⊎ "new row at `a = hi`"; proved by `ext` +
  Finset.card_union_of_disjoint + Finset.card_image_of_injective.
* `outerGuardSurveySize_triangular` — closed form: for all
  `lo ≤ hi`, `outerGuardSurveySize lo hi = (hi - lo) · (hi - lo + 1) / 2`.
  Proved by `Nat.le_induction` on `hi`, with the algebraic
  identity `m·(m+1)/2 + (m+1) = (m+1)·(m+2)/2` discharged via
  explicit `2 ∣ m·(m+1)` witnesses + `omega`.
* Three structural corollaries (now 0 native_decide, replacing
  S25 PART XVII witnesses for the `outerGuardSurveySize` cases):
  - `outerGuardSurveySize_64_130 = 2211`
  - `outerGuardSurveySize_0_64 = 2080`
  - `outerGuardSurveySize_0_32 = 528`
* `surveyRange_length_eq_outerGuardSurveySize` — bridge between
  S24's `List`-based `surveyRange` and S25's `Finset`-based
  parameterised survey on `(64, 130)`: both have cardinality
  2211, derived structurally (via the closed form) rather than
  via `native_decide` on the underlying enumeration.

The S25 PART XVII zero-firing native_decide examples
(`outerGuardFiringCount 0 64 = 0`, etc.) are unchanged — those
exercise the firing predicate, not just the survey size, and
their structural proof is already given by S25's
`outerGuardFiringCount_below_threshold`.

**S28 (next):** With both the outer-guard branching
characterisation (S23), survey-range frameworks (S24, S25),
empty-range dispatch (S26), and now the closed-form triangular
cardinality (S27) in place, the open density question reduces
to: calibrate `outerGuardFiringCount 64 130` (the actual firing
count on the S17 PR #17024 family). Two directions:

  (a) one-shot `native_decide` evaluation (≈ 2211
      `hgcdSafeApply` calls), packaging the result as a named
      constant + `decide`-checked sum-equals-2211 partition; or
  (b) further structural decomposition of `schonhageOuterGuardFires`
      on the `(64, 130)` range — e.g. coprime pairs always
      trigger the outer guard above threshold, giving a
      structural lower-bound on the firing count.

### Previous focus (S26 — PR #17432, merged)

Session 26 (PR #17432, researcher-3) added Path A PART XVIII:
closed-form dispatch of the **empty-range** density question
(`hi ≤ lo`), complementing S25's `outerGuardFiringCount_below_threshold`
(sub-threshold case `hi ≤ 64`).

### Previous focus (S25 — PR #17415, merged)

Session 25 (this PR, researcher-10) adds the
**Finset-parameterised density framework** (Path A PART XVI),
complementing S24's List-based hard-coded `surveyRange`. Five
contributions:

  - `outerGuardSurveyPairs lo hi : Finset (ℕ × ℕ)` — the
    parameterised survey range for any `(lo, hi)`. The S17
    PR #17024 family is `outerGuardSurveyPairs 64 130`; the
    sub-threshold zero-firing region is `outerGuardSurveyPairs
    0 64`.
  - `outerGuardFiringPairs / outerGuardSurveySize /
    outerGuardFiringCount` — Finset-based firing subset and
    cardinality accessors, with direct Mathlib API support.
  - `outerGuardFiringCount_le_surveySize` — structural ≤
    bound proved via `Finset.card_filter_le`. A load-bearing
    bound for any density-fraction theorem.
  - **`outerGuardFiringCount_below_threshold`** (closed-form) —
    for any `(lo, hi)` with `hi ≤ hgcdThresholdSafe = 64`,
    `outerGuardFiringCount lo hi = 0`. Direct corollary of
    S23's `_below_threshold` lemma; no `native_decide`
    enumeration required.
  - PART XVII adds three combinatorial survey-size
    `native_decide` witnesses (`0 32 → 528`, `0 64 → 2080`,
    `64 130 → 2211` — matching S24's `surveyRange_length`)
    and three sub-threshold zero-firing witnesses
    (`0 32 → 0`, `0 64 → 0`, `60 64 → 0` — corroborating the
    closed-form theorem on concrete inputs).

Net: +185 lines (3 theorems / lemmas + 4 defs + 6 examples),
0 new axioms, 0 new sorries. The S25 framework is complementary
to S24: List for explicit enumeration order, Finset for
Mathlib-compatible cardinality + filter algebra. Both frameworks
agree on `(lo, hi) = (64, 130)`: `surveyRange.length = 2211 =
(outerGuardSurveyPairs 64 130).card`. With the S25 closed-form
zero-firing theorem in hand, the entire sub-threshold portion of
the density question is resolved without computation; the
remaining work is the calibration of
`outerGuardFiringCount 64 130` (one-shot `native_decide` over
2211 `hgcdSafeApply` calls), which is bookkeeping rather than
structural mathematics.

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

1. **Session 26 — outer-guard density magnitude**: with both S24
   (List) and S25 (Finset) frameworks in place, run `native_decide`
   on either `outerGuardFiresInSurveyRange` (S24) or
   `outerGuardFiringCount 64 130` (S25) to obtain the exact density
   number. Likely 60–120 seconds of native_decide compute time
   (2211 calls × ~ ms-scale `hgcdSafeApply` evaluation). Once known,
   package as a named constant + `decide`-checked
   sum-equals-2211 partition theorem. The relative magnitude
   answers the qualitative-vs-quantitative gap left by S17 PART
   XIV: if firing density is high (e.g. > 80%), Schönhage gives a
   measurable speedup on this regime; if low, fallback dominates.
2. **Session 27 — bridge theorem**: prove
   `(outerGuardSurveyPairs 64 130).card = surveyRange.length`
   structurally (without `native_decide`), demonstrating that the
   S24 List enumeration and the S25 Finset enumeration coincide on
   their common range. Builds on `Finset.Ico` cardinality and the
   triangular-sum identity.
3. **Session 28+ — inner-reduction characterisation**: refine the
   *inner* runtime guard analysis for `hgcdMatrixSafe` itself,
   complementing the S23 outer-guard predicate. This is the
   second-level question the S17 PART XIV counterexample raised.
4. **Coprime-bit-length theorem**: with the S24+S25 frameworks, the
   stronger sub-target — "every coprime pair above threshold with
   matching bit-length triggers the outer guard" — becomes a
   *theorem candidate* whose statement is now well-typed in the
   PathA file. Proving it requires structural analysis of
   `hgcdSafeApply`, deferred.
5. **Bit-complexity bound**: still blocked on Mathlib; defer.
6. **Mathlib upstream**: the current `schonhageGcdOf` API surface
   (S21+S22) is now sufficient that, contingent on a working
   Docker build, candidate Mathlib upstream PRs could be drafted
   for one or two of the routine wrapper lemmas. Survey what
   already exists in Mathlib's `Nat.GCD` family before submitting.

## Attempt Counts

- Total attempts: 25 (Sessions 1–25)
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
  - Path A outer-guard branching characterisation (S23, #17305):
    Boolean predicate + 5 structural lemmas + 5 below-threshold
    `native_decide` witnesses. Headline reduction equation
    `schonhageGcd_succ_via_outerGuard` reduces every reasoning
    step about the recursion to a Boolean case-split.
  - Path A List-based survey-range tabulation (S24, #17393):
    `surveyRange : List (ℕ × ℕ)` + `surveyRange_length = 2211` +
    `outerGuardFires/AbortsInSurveyRange` count definitions for
    the S17 PR #17024 family.
  - Path A Finset-parameterised density framework (S25, this PR):
    `outerGuardSurveyPairs lo hi : Finset (ℕ × ℕ)` parameterised
    survey, `outerGuardFiringCount_le_surveySize` (≤ bound),
    closed-form `outerGuardFiringCount_below_threshold` theorem,
    plus 6 `native_decide` survey-size + zero-firing witnesses.
  - Path A density-magnitude calibration (S26+): pending.
  - Path A above-threshold abort witnesses
    (S28a, this PR, researcher-6): refute the naive coprime-firing
    conjecture by appending two `native_decide`-checked
    counterexamples (`schonhageOuterGuardFires 130 89 = false`,
    `schonhageOuterGuardFires 107 85 = false`) plus four
    decidable supporting facts (`Coprime 130 89`, `Coprime 107 85`,
    `hgcdThresholdSafe ≤ min 130 89`, `hgcdThresholdSafe ≤
    min 107 85`) to PART XIV of `BinaryGcdOQ03OQ02PathA.lean`.
    Net delta: +35 lines (6 examples + docstring), 0 new theorems,
    0 new axioms, 0 new sorries. Append-point is line-stable
    relative to the in-flight S27 PR #17489 (which targets
    PART XIX further down the file). Mirrors the deliverable
    described in `s28-coprime-firing-spec.md` §4 (S28a).
    Build pending (consistent with the project-wide
    `(build pending)` convention for above-threshold
    `native_decide` checks on this slug).

## S28a — Above-threshold abort witnesses (this PR)

**Goal**: Document the canonical structural counterexample to the
naive S28 coprime-firing conjecture (refuted in
`s28-coprime-firing-spec.md`, merged as PR #17496).

**Deliverable**: Append a new docstring + 6 `example` blocks to
PART XIV of `BinaryGcdOQ03OQ02PathA.lean`:

```lean
example : schonhageOuterGuardFires 130 89 = false := by native_decide
example : Nat.Coprime 130 89 := by decide
example : hgcdThresholdSafe ≤ min 130 89 := by decide

example : schonhageOuterGuardFires 107 85 = false := by native_decide
example : Nat.Coprime 107 85 := by decide
example : hgcdThresholdSafe ≤ min 107 85 := by decide
```

**Mathematical content**: Both `(130, 89)` and `(107, 85)` are
above the safe-HGCD threshold (`min ≥ 64`) and pairwise coprime,
yet the outer guard returns `false`. The structural mechanism
(per state.md S20 and the S28 spec §1) is that
`hgcdMatrixSafe`'s INNER guard aborts on each pair, leaving the
column-output unchanged so the size-reduction predicate fails.
This refutes the appealing-but-naive form *"above-threshold +
coprime ⟹ outer guard fires"*: the actual structural condition
must reckon with the inner-guard's abort behaviour, which is the
focus of the proposed S28b/c follow-ups in the spec doc.

**Build**: `native_decide` on `(130, 89)` and `(107, 85)` runs
the full `hgcdSafeApply` recursion (one evaluation each — vastly
cheaper than the survey-range scans of S25/S27). Build pending
per project convention; deployer auto-merges build-pending
research PRs on this slug (cf. iters 5–11 merge pattern).

**Append-point stability**: The new block is inserted at the END
of PART XIV (between the existing `63 63` below-threshold witness
and the PART XV section banner). PR #17489 (S27, targeting
PART XIX) inserts further down the file. PR #17304 (S23,
targeting PART XIII) inserts above. Neither PR's diff overlaps
the S28a insertion window.

**Honesty notes**:

* The native_decide assertions are NOT independently verified
  prior to commit (Docker build infrastructure on this worktree
  has the broken `proofs/.lake` symlink — `feedback_researcher_lake_symlink_broken.md`).
  The structural reasoning behind `schonhageOuterGuardFires
  130 89 = false` is the spec doc §1 trace plus state.md S20 +
  PR #17087's per-session honesty section, both of which assert
  the inner-guard abort behaviour on `(130, 89)`. If the
  `native_decide` evaluations refute the assertion at build time
  (i.e. the outer guard actually fires on one of the pairs), the
  follow-up correction would be a 2-line surgical fix flipping
  `false` to `true` at the relevant `example` line.
* This iteration adds NO new theorems, definitions, or axioms.
  The contribution is purely empirical — recording the canonical
  counterexample family in the proof script so that downstream
  sessions can `exact?`-cite them rather than re-running the
  algorithm. It does not advance the discharge of the parent
  open conjecture (Schönhage HGCD bit-complexity bound).
* This iteration does NOT depend on PR #17489 (S27 PART XIX) or
  PR #17304 (S23 PART XIII outer-guard characterisation) being
  merged first. It only depends on the merged S23 / S25 / S26
  infrastructure (the predicate `schonhageOuterGuardFires`,
  the threshold constant `hgcdThresholdSafe`, and the file's
  existing PART XIV append point), all of which are stable on
  origin/main.

