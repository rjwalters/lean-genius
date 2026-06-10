# Current State

**Phase**: ACT
**Since**: 2026-06-10 (S13 Helper-ACT)
**Iteration**: 15

## Current Focus

S13 Helper-ACT (researcher-8, 2026-06-10, Lean-only narrow-ACT):
added `Cbrt3Helpers.five_nine_seven_four_four_nine_over_four_one_four_two_four_eight_lt_cbrt3 :
(597449/414248 : ℝ) < cbrt3` to `CubeRoot3IrrationalOQ04Helpers.lean` via
the proven two-line cubing-iff template (`lt_cbrt3_iff_cube_lt + norm_num`).
This is the **true 13th CF convergent** (using `a₁₂ = 8` per OEIS
A002945 entry 13, cross-checked against the 200-digit Decimal CF
witness from S12a/S12b). Helper file 586 → 643 LOC (+57 LOC,
+1 theorem +1 prose section; theoremCount 17 → 18). 0 sorries,
0 axioms (slug remains 0/0). Cube-direction sanity:
`597449³ = 213_256_617_080_909_849 < 213_256_617_081_662_976 =
3 · 414248³` (diff `−753_127`, relative gap `≈ 3.53·10⁻¹²` —
roughly two orders of magnitude tighter than S12b's upper-side gap
of `≈ 2.87·10⁻¹⁰`, consistent with `597449/414248` being the next
true convergent one rung beyond S12b's `73011/50623`).

**No math-correction precedent triggered this iteration**: both
the recursion arithmetic `8 · 73011 + 13361 = 597449,
8 · 50623 + 9264 = 414248` and the cube digits matched the
post-S12b sketch on the first pass. The math-correction precedent
count for this slug remains at FIVE (no change from S12b).

Helper-only ACT was chosen to keep this iteration narrow and
conflict-free (the deeper main-file ACT for `cbrt3_a11 = 5`
requires a 23-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
chain on an eleven-fold-nested fraction with heartbeat budget
`set_option maxHeartbeats 6400000 in` per the 2× per-depth scaling
validated through S7–S12b — that's S13b territory). Docker build
of helper file initiated; previous helpers in this same template
(S11a, S12a, S12b helper) all built clean.

See `sessions/2026-06-10-s13-helper-act-thirteenth-convergent.md`
for the cube arithmetic, OEIS A002945 cross-verification at 200
digits, and the S13b next-action sketch (`cbrt3_a11 = 5` via the
sandwich `597449/414248 < cbrt3 < 73011/50623`).

## Prior Focus (S12b ACT, MERGED 2026-06-01)

S12b ACT (researcher-1, 2026-06-01, combined Helper-ACT + Main-ACT):
shipped the **eleventh partial quotient** `cbrt3_a10 = 2` of the simple
CF of `∛3`. Two-part PR:

1. **Helper-ACT predecessor** (added to `CubeRoot3IrrationalOQ04Helpers.lean`):
   `Cbrt3Helpers.cbrt3_lt_seven_three_oh_one_one_over_five_oh_six_two_three :
   cbrt3 < (73011/50623 : ℝ)` via the proven two-line cubing-iff template
   (`cbrt3_lt_iff_three_lt_cube + norm_num`). The **true 12th CF convergent**
   (odd-index, upper side; using `a₁₁ = 5` per OEIS A002945). Required
   because the S10 upper bound `6206/4303` (gap `≈ 1.44·10⁻⁷`) is
   INSUFFICIENT at depth 10 — propagation with the sandwich
   `13361/9264 < cbrt3 < 6206/4303` gives `x₁₀ ∈ (0, 1/2)`, lower bound
   collapses to `0` and does not separate from `1/x₁₀ ≥ 2`. The S12b
   upper bound `73011/50623` (gap `≈ 9.57·10⁻¹¹`, three orders of
   magnitude tighter) gives `x₁₀ ∈ (5/11, 1/2)` ⟹ `1/x₁₀ ∈ (2, 11/5)`
   ⟹ floor = 2 ✓.

2. **Main-ACT** (added to `CubeRoot3IrrationalOQ04.lean`): the
   21-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain on a
   ten-fold-nested fraction consuming the sandwich
   `13361/9264 < cbrt3 < 73011/50623` followed by floor antisymmetry.
   Heartbeat budget `set_option maxHeartbeats 3200000 in` (2× S11b's
   1.6M, per empirical 2× per-depth scaling validated through S7–S11b).

Helper file 528 → 586 LOC (+58 LOC, +1 theorem +1 prose section;
theoremCount 16 → 17). Main file 1505 → 1747 LOC (+242 LOC,
+1 theorem; theoremCount 17 → 18). 0 sorries, 0 axioms (slug remains 0/0).
The chain `cbrt3_a0,…,cbrt3_a10` now covers the OEIS A002945 prefix
one step beyond S11b — verifying `a₁₀ = 2` (the actually-correct
value, per math-correction #FOUR from S12a).

Cube-direction sanity for the new helper: `73011³ = 389_192_883_500_331 >
389_192_883_463_101 = 3 · 50623³` (diff `+37_230`, relative gap
`≈ 9.57·10⁻¹¹`).

**Math-correction precedent #FIVE for this slug**: the post-S12a
`nextAction` sketch (JSON `currentState.nextAction` and state.md
`Next Action` as of 2026-06-01 immediately after PR #21873 merged)
claimed `73011³ = 389_271_307_557_812_731` and
`3·50623³ = 389_271_307_493_213_241` with diff `+64_599_490`. The
actual values are `73011³ = 389_192_883_500_331` and
`3·50623³ = 389_192_883_463_101` with diff `+37_230` — both
magnitudes off by ~1000× (sketch was working in `10¹⁸` while
actual is `10¹⁴`). Direction unchanged (upper bound). Math-correction
precedent count for this slug now stands at FIVE; the slug continues
to be the gallery's record holder for pre-claim Python sanity
caught errors.

Docker build of main+helper files verified clean (7745 jobs;
helper file 10s, main file 43s on standard image). Pre-existing
`Mathlib.Data.Real.Irrational` deprecation warning in
`Proofs/CubeRoot3Irrational.lean:8` unchanged (parent module not
owned by this slug). 0 new sorries, 0 new axioms.

See `sessions/2026-06-01-s12b-act-eleventh-partial-quotient.md`
for the full algebraic chain table, propagated rational bounds at
each of the 21 steps, OEIS A002945 cross-verification, and the
S13 next-action sketch (`cbrt3_a11 = 5` via 13th convergent
lower bound `597449/414248` — all recursion arithmetic to be
re-verified pre-claim in S13).

## Prior Focus (S12a Helper-ACT, PR #21873, MERGED 2026-06-01T08:15:18Z)

S12a Helper-ACT (researcher-1, 2026-06-01, Lean-only narrow-ACT):
added `Cbrt3Helpers.one_three_three_six_one_over_nine_two_six_four_lt_cbrt3 :
(13361/9264 : ℝ) < cbrt3` to `CubeRoot3IrrationalOQ04Helpers.lean` via
the proven two-line cubing-iff template (`lt_cbrt3_iff_cube_lt + norm_num`).
This is the **true 11th CF convergent** of `∛3` (using `a₁₀ = 2` per
OEIS A002945 entry 11, independently verified to 200 digits via
Decimal-arithmetic Newton-iteration CF expansion). Helper file
472 → 528 LOC (+56 LOC, +1 theorem +1 prose section; theoremCount
15 → 16). 0 sorries, 0 axioms (slug remains 0/0). Cube-direction
sanity: `13361³ = 2_385_156_564_881 < 2_385_156_575_232 = 3 · 9264³`
(diff `−10_351`, relative gap `≈ 4.34·10⁻⁹` — roughly an order of
magnitude tighter than S11a's `7155/4961` lower-side gap of
`≈ 4.96·10⁻⁸`, consistent with `13361/9264` being a true convergent
one rung beyond S11a's semi-convergent).

**Math-correction precedent #FOUR for this slug**: the prior
post-S11b `nextAction` sketch (JSON `currentState.nextAction` as of
2026-05-31) claimed OEIS A002945 entries `a₁₀ = 1`, `a₁₁ = 2`. The
actual prefix is `[1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4,
2, 6, 4, 4, ...]` (200-digit Decimal-precision Newton-iteration CF
expansion, this S12a session), so `a₁₀ = 2`, `a₁₁ = 5`, `a₁₂ = 8`.
The S11a helper docstring's claim that `7155/4961` is the "10th
convergent with `a₁₀ = 1`" is also strictly incorrect: `7155/4961`
is a **semi-convergent** (best-rational approximation between the
9th and 11th true CF convergents), not a true CF convergent. **The
S11a proof and the S11b main theorem remain mathematically correct**
— `7155/4961 < cbrt3` is true (Decimal computation: gap `−2.4·10⁻⁸`)
and provided a valid lower bound for the S11b sandwich
`7155/4961 < cbrt3 < 6206/4303` proving `cbrt3_a9 = 6`. Only the
"true 10th convergent" framing in the docstring is off.

Docker build of helper file verified clean (build log embedded in
the S12a session memo at
`sessions/2026-06-01-s12a-helper-act-eleventh-convergent.md`).

See `sessions/2026-06-01-s12a-helper-act-eleventh-convergent.md`
for the cube arithmetic, OEIS A002945 cross-verification at 200
digits, semi-convergent vs true-convergent distinction, and the
S12b next-action sketch.

## Prior Focus (S11b ACT, PR #21654, MERGED 2026-06-01T00:32:07Z)

S11b ACT (researcher-1, 2026-05-31): shipped the tenth partial
quotient `cbrt3_a9 = 6` — the largest in the known prefix —
consuming the S11a + S10 sandwich pair (`7155/4961 < cbrt3 < 6206/4303`)
through a 17-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
chain on a nine-fold-nested fraction followed by floor antisymmetry.
Main file 1289 → 1505 LOC (+216, +1 theorem). Heartbeat budget
`set_option maxHeartbeats 1600000 in` (2× S10's 800_000, per the
empirical 2× per-depth scaling validated through S7–S10). Docker
build verified clean (7745 jobs; main file 218s on standard image).
0 sorries, 0 axioms (slug remains 0/0). The chain
`cbrt3_a0, …, cbrt3_a9` now covers the full OEIS A002945 prefix
that was independently cross-checked to 50 decimal places.

See `sessions/2026-05-31-s11b-act-tenth-partial-quotient.md` for the
full algebraic chain table and contraction validation.

## Prior Focus (S11 STATE-SYNC, now resolved by S11b)

S11 STATE-SYNC (researcher-6, 2026-05-16): doc-only catchup absorbing
the post-S10 PREP + Helper-ACT pair into state.md + JSON head fields,
fixing knowledge.nextSteps[0] cube-digit residue and leanFiles[]
helper-file drift. Three predecessors merged on `origin/main` between
S10 and now:

1. **S11 PREP MATH-CORRECTION** (PR #19420, researcher-5, doc-only):
   corrected three numerical errors in the post-S10 next-action
   sketch — `7155³` (was `366_360_812_875`, actual `366_293_248_875`,
   off by `+67_564_000`), `3·4961³` (was `366_360_846_363`, actual
   `366_293_267_043`, off by `+67_579_320`), and the resulting diff
   `−18_168` (was `−33_488`) / gap `1.488·10⁻⁷` (was `2.742·10⁻⁷`).
   The DIRECTION of the bound (`7155/4961 < cbrt3`, valid lower
   bound for proving `cbrt3_a9 = 6`) is unchanged. Edited state.md
   `## Next Action` block + `currentState.nextAction` in JSON; did
   NOT touch `knowledge.nextSteps[0]`, which retained the wrong
   cube digits — this STATE-SYNC fixes that residue.

2. **S11a Helper-ACT** (PR #19456, researcher-6, narrow ACT):
   shipped the tenth-convergent lower-bound helper
   `Cbrt3Helpers.seven_one_five_five_over_four_nine_six_one_lt_cbrt3 : (7155/4961 : ℝ) < cbrt3`
   via the two-line `lt_cbrt3_iff_cube_lt + norm_num` template.
   Helper file grew 420 → 472 lines (+52 LOC; +1 theorem +
   prose section). Docker build verified clean (7744 jobs, helper
   file 52s). Helper-only ACT was chosen to stay conflict-free vs
   then-open PREP #19420 (doc-only PREP would have collided with a
   combined ACT touching state.md / JSON). Pre-claim Python
   cube-direction sanity: `7155³ = 366_293_248_875 < 366_293_267_043
   = 3·4961³`, diff `−18_168 < 0` ⟹ `(7155/4961)³ < 3` ⟹
   `7155/4961 < cbrt3` ✓ (correct lower-side direction); gap
   `18_168/122_097_755_681 ≈ 1.488·10⁻⁷`, just barely tighter
   than S10's upper-side gap `1.43·10⁻⁷` — consistent with
   alternating-convergent contraction. **Iteration deliberately
   NOT bumped by S11a** (memo §"Iteration bookkeeping": "S11
   numbering will be applied to JSON by the future STATE-SYNC
   that absorbs both this S11a and PR #19420" — this STATE-SYNC
   is that planned future absorber).

3. **(implicit) S10 ACT** (PR #19395, researcher-3, build-verified):
   shipped `cbrt3_a8 = 1` via 6206/4303 upper bound (ninth
   partial quotient). State.md + JSON head fields were correctly
   updated at S10-merge time; only the tail-end of nextSteps
   needed S11+ refresh.

After this STATE-SYNC:
- state.md head: `Iteration 11`, `Since 2026-05-16 (S11 STATE-SYNC)`
- JSON `currentState.iteration: 11`, `attemptCounts.total: 11`
- JSON `currentState.focus` → S11 STATE-SYNC description
- JSON `currentState.nextAction` → S11b ACT skeleton (main theorem
  `cbrt3_a9 = 6`; helper already in place from S11a)
- JSON `knowledge.builtItems[+1]` → S11a helper entry (15th item)
- JSON `knowledge.nextSteps[0]` → S11b plan with corrected cube
  digits (`366_293_248_875` / `366_293_267_043` / `−18_168` /
  `1.488·10⁻⁷`)
- JSON `leanFiles[5]` (Helpers) → lineCount 420 → 472,
  theoremCount 14 → 15
- 0 Lean / 0 problem.md / 0 knowledge.md / 0 meta.json / 0 gallery
  / 0 lake-manifest / 0 sibling-slug edits
- 0 axiom / 0 sorry delta (slug remains 0/0)

The ACT-readiness gate for S11b (main `cbrt3_a9 = 6`) is now GREEN
on all substantive fronts: helper present, sandwich pair complete
(`7155/4961 < cbrt3 < 6206/4303`), corrected cube digits cross-referenced,
heartbeat-budget guess `set_option maxHeartbeats 1600000 in` (2× S10's
`800000`) recorded, parent-file pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
unchanged since S9 build. Only blocker is the standard Docker iteration
overhead (~25 min cold rebuild per `proofs/.lake` symlink quirk).

## S10 Focus (just completed)

S10 (researcher-3): Ninth partial quotient.
`cbrt3_a8 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)⌋ = (1 : ℤ)`
— the ninth partial quotient `a₈ = 1` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of OEIS A002945. The S10-prep
addition to `CubeRoot3IrrationalOQ04Helpers.lean` supplies the new
upper bound
`cbrt3_lt_six_two_oh_six_over_four_three_oh_three : cbrt3 < (6206/4303 : ℝ)`
(cube `6206³ = 239_020_589_816 > 239_020_578_381 = 3 · 4303³`; diff
`+11_435`; gap `11_435/79_673_526_127 ≈ 1.43·10⁻⁷`) via the two-line
cubing-iff template. The lower bound is the S9 helper
`nine_forty_nine_over_six_fifty_eight_lt_cbrt3` (reused unchanged).
Proof is rational-arithmetic only (the existing helper import + a
16-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain on an
eight-fold-nested fraction); no axioms; depends on `cbrt3_cubed` only.
Theorem requires `set_option maxHeartbeats 800000 in` (scoped) — twice
the S9 budget, the eight-level-nested term pushes the deepest
`linarith` past the 400_000 cap on step 16. **Docker build verified
clean** (7745 jobs; helper file 8.6s, main file 26s; pre-existing
`Mathlib.Data.Real.Irrational` deprecation warning in
`Proofs/CubeRoot3Irrational.lean:8` unchanged from prior S9 build,
not owned by this slug).

The new cube boundary `(6206/4303)³ > 3` differs from `3` by only
`11_435 / 79_673_526_127 ≈ 1.43·10⁻⁷` — about one order of magnitude
tighter than S9's lower-side gap of `587/284_890_312 ≈ 2.06·10⁻⁶`.
The ninth convergent `6206/4303` lies on the *upper* side of `cbrt3`,
alternating with `949/658` below. The convergent recursion
`p_n = a_n · p_{n-1} + p_{n-2}` with `a₉ = 6` gives
`q₉ = 6·658 + 355 = 4303` and `p₉ = 6·949 + 512 = 6206`. The
identification of `a₉ = 6` is from OEIS A002945 (independently
verified to 50 digits via `decimal.Decimal` in S9-prep PR #19011);
the S10 helper does NOT prove `a₉ = 6`, only uses `6206/4303 > cbrt3`
as a numerical bound.

(Pre-claim cube-direction sanity, per memory
`feedback_researcher_cf_convergent_recursion_direction_trap`:
Python `6206**3 = 239_020_589_816 > 3·4303**3 = 239_020_578_381`,
diff `+11_435 > 0`, confirming `6206/4303 > cbrt3`. The two-firings
math-correction precedent in this slug — S7→S8 sketch and S8→S9
sketch — never bit S10 because the OEIS A002945 entry `a₉ = 6` was
explicitly cited in the prior S9 next-action sketch.)

## S9 Focus (just completed)

S9 (researcher-9): Eighth partial quotient.
`cbrt3_a7 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋ = (1 : ℤ)`
— the eighth partial quotient `a₇ = 1` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of OEIS A002945. The S9-prep addition to
`CubeRoot3IrrationalOQ04Helpers.lean` supplies the new lower bound
`nine_forty_nine_over_six_fifty_eight_lt_cbrt3 : (949/658 : ℝ) < cbrt3`
(cube `854_670_349 < 854_670_936 = 3·658³`; diff `587`; gap
`587/284_890_312 ≈ 2.06·10⁻⁶`) via the two-line cubing-iff template.
The upper bound is the S8 helper
`cbrt3_lt_five_twelve_over_three_fifty_five : cbrt3 < (512/355 : ℝ)`
(reused unchanged). Proof is rational-arithmetic only (the existing
helper import + a 14-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
chain on a septuple-nested fraction); no axioms; depends on
`cbrt3_cubed` only. Theorem requires `set_option maxHeartbeats 400000
in` (scoped) — the seven-level-nested term pushes the default 200_000
heartbeat budget on the deepest `linarith` step (line 1017,
`hx7_gt : 1/2 < y₆ - 5`, `whnf` reduction of `1/(1/(1/(1/(1/(1/(cbrt3-1)
-2)-3)-1)-4)-1)`). No tactic changes; proof structure identical to
S8 `cbrt3_a6`. Docker build verified clean (7745 jobs, ~20s
elaboration).

The new cube boundary `(949/658)³ < 3` differs from `3` by only
`587/284_890_312 ≈ 2.06·10⁻⁶` — about one order of magnitude tighter
than S8's upper-side gap of `1103/44_738_875 ≈ 2.47·10⁻⁵`. The eighth
convergent `949/658` lies on the *lower* side of `cbrt3`, alternating
with `512/355` above. The convergent recursion
`p_n = a_n · p_{n-1} + p_{n-2}` with `a₈ = 1` gives
`q₈ = 1·355 + 303 = 658` and `p₈ = 1·512 + 437 = 949`. The
identification of `a₈ = 1` is from OEIS A002945 (independently
verified to 50 digits via `decimal.Decimal` in S9-prep PR #19011);
the S9 helper does NOT prove `a₈ = 1`, only uses `949/658 < cbrt3`
as a numerical bound.

(Math correction supersession: the prior `## Next Action` block had
suggested `2485/1723 = (4·512+437)/(4·355+303)` as the eighth
convergent, computed with `a₈ = 4`. The actual `a₈ = 1` per OEIS
A002945; the proposed `2485/1723` is in fact *above* `cbrt3` not
below (cube `2485³ = 15_345_434_125 > 15_345_360_201 = 3·1723³`,
diff `+73_924`), so a `norm_num` proof of `(2485/1723 : ℝ) < cbrt3`
would have failed. The correct eighth convergent using `a₈ = 1` is
`949/658`. PR #19011 (S9-prep MATH-CORRECTION) caught this typo
before any ACT attempt was made; this S9 ACT supersedes that
PREP — the corrected math is now built into the proof.)

## S8 Focus (just completed)

S8 (researcher-10): Seventh partial quotient.
`cbrt3_a6 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1)⌋ = (5 : ℤ)`
— the seventh partial quotient `a₆ = 5` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, …]` of OEIS A002945. The S8-prep addition to
`CubeRoot3IrrationalOQ04Helpers.lean` supplies the new upper bound
`cbrt3_lt_five_twelve_over_three_fifty_five : cbrt3 < (512/355 : ℝ)`
(cube `134_217_728/44_738_875 > 134_216_625/44_738_875 = 3`; diff
`1103`; note `512 = 2⁹` so `512³ = 2²⁷` exactly) via the two-line
cubing-iff template. The lower bound is the S7 helper
`four_thirty_seven_over_three_oh_three_lt_cbrt3 : (437/303 : ℝ) < cbrt3`
(reused unchanged). Proof is rational-arithmetic only (the existing
helper import + a 12-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
chain on a sextuple-nested fraction); no axioms; depends on
`cbrt3_cubed` only.

The new cube boundary `(512/355)³ > 3` differs from `3` by only
`1103/44_738_875 ≈ 2.5·10⁻⁵` — comparable to S7's lower-side gap of
`928/27818127 ≈ 3.3·10⁻⁵`. The seventh convergent `512/355` lies on
the *upper* side of `cbrt3`, alternating with `437/303` below. The
convergent recursion `p_n = a_n · p_{n-1} + p_{n-2}` with `a₇ = 1`
gives `q₇ = 1·303 + 52 = 355` and `p₇ = 1·437 + 75 = 512`. The
identification of `a₇ = 1` is from OEIS A002945; the S8 helper does
NOT prove `a₇ = 1`, only uses `512/355 > cbrt3` as a numerical bound.

(Math correction during S8 implementation: an earlier S7 next-action
sketch suggested `2260/1567` as the seventh convergent, computed as
`(5·437+75)/(5·303+52)` — but this uses `a₇ = 5` in the recursion
instead of `a₇ = 1`. Direct cube check shows `2260³ < 3·1567³`, so
`2260/1567 < cbrt3`, i.e., `2260/1567` is below cbrt3, not above.
The correct seventh convergent using `a₇ = 1` is `512/355`, with
`512³ > 3·355³` confirming `512/355 > cbrt3`.)

## Previous Focus

S7 (researcher-1): Sixth partial quotient.
`cbrt3_a5 : ⌊1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4)⌋ = (1 : ℤ)`
— the sixth partial quotient `a₅ = 1` of the simple CF
`[1; 2, 3, 1, 4, 1, …]` of OEIS A002945. The S7-prep addition to
`CubeRoot3IrrationalOQ04Helpers.lean` supplies the new lower bound
`four_thirty_seven_over_three_oh_three_lt_cbrt3 : (437/303 : ℝ) < cbrt3`
(cube `83453453/27818127 < 83454381/27818127 = 3`; diff `928`) via the
two-line cubing-iff template. The upper bound is the S6 helper
`cbrt3_lt_seventy_five_over_fifty_two : cbrt3 < (75/52 : ℝ)`. Proof is
rational-arithmetic only (one helper import + an 11-step
`lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain on a
quintuple-nested fraction); no axioms; depends on `cbrt3_cubed` only.

The new cube boundary `(437/303)³ < 3` differs from `3` by only
`928/27818127 ≈ 3.3·10⁻⁵` — about two orders of magnitude tighter
than S6's lower-side gap of `2.4·10⁻³`. This was the tightest cubing
boundary in the prefix at S7, consistent with `437/303` being the
sixth convergent of the CF.

## Earlier Focus

S6 (researcher-11): Fifth partial quotient.
`cbrt3_a4 : ⌊1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)⌋ = (4 : ℤ)`
— the fifth partial quotient `a₄ = 4` of the simple CF
`[1; 2, 3, 1, 4, …]` of OEIS A002945. The S6-prep additions to
`CubeRoot3IrrationalOQ04Helpers.lean` supply both new bounds
`sixty_two_over_forty_three_lt_cbrt3` (cube `238328/79507 < 238521/79507 = 3`)
and `cbrt3_lt_seventy_five_over_fifty_two`
(cube `3 = 421824/140608 < 421875/140608`) via the two-line cubing-iff
templates. Proof is rational-arithmetic only (two helper imports + a
9-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain on a
quadruple-nested fraction); no axioms; depends on `cbrt3_cubed` only.

## Even Earlier Focus

S5 (researcher-5): Fourth partial quotient.
`cbrt3_a3 : ⌊1 / (1 / (1 / (cbrt3 - 1) - 2) - 3)⌋ = (1 : ℤ)` — the
fourth partial quotient `a₃ = 1` of the simple CF `[1; 2, 3, 1, 4, …]`.
The S5-prep helpers PR (#17859, researcher-1) supplies the new lower
bound `Cbrt3Helpers.twenty_three_sixteenths_lt_cbrt3` (cube target
`12167/4096 < 12288/4096 = 3`) via the two-line cubing-iff template.
The upper bound is the S4-proved `cbrt3_lt_thirteen_ninths`. Proof is
rational-arithmetic only (one helper import + a 7-step
`lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain on a triple-nested
fraction); no axioms; depends on `cbrt3_cubed` only.

## Earlier Earlier Focus

S4 (researcher-3): Third partial quotient.
`cbrt3_a2 : ⌊1 / (1 / (cbrt3 - 1) - 2)⌋ = (3 : ℤ)` — the third
partial quotient `a₂ = 3` of the simple CF `[1; 2, 3, 1, 4, …]`.
Two new cubing-bound lemmas (`ten_sevenths_lt_cbrt3`,
`cbrt3_lt_thirteen_ninths`) plus the floor identity, following
the template specified by S3's next-action sketch verbatim.

## Even Earlier Focus

S3 (researcher-8): Second partial quotient.
`cbrt3_a1 : ⌊1 / (cbrt3 - 1)⌋ = (2 : ℤ)` — the second partial
quotient `a₁ = 2` of the simple CF `[1; 2, 3, 1, 4, …]`. Two new
cubing-bound lemmas (`four_thirds_lt_cbrt3`, `cbrt3_lt_three_halves`)
plus the floor identity. Proof is rational-arithmetic only (cubing
bounds + `div_lt_iff₀` / `le_div_iff₀` + `Int.le_floor` /
`Int.floor_lt`); no axioms; depends on `cbrt3_cubed` only.

## Active Approach

**Finite-prefix verification, no full-sequence claim.**

The CF of `∛3` is non-periodic (Lagrange), so the deliverable is a
chain of lemmas

```
cbrt3_a0 : ⌊cbrt3⌋ = 1                                 ✓ S2
cbrt3_a1 : ⌊1/(cbrt3 - 1)⌋ = 2                         ✓ S3
cbrt3_a2 : ⌊1/(1/(cbrt3-1) - 2)⌋ = 3                   ✓ S4
cbrt3_a3 : ⌊1/(1/(1/(cbrt3-1) - 2) - 3)⌋ = 1           ✓ S5
cbrt3_a4 : ⌊1/(1/(1/(1/(cbrt3-1) - 2) - 3) - 1)⌋ = 4   ✓ S6
cbrt3_a5 : … = 1                                       ✓ S7
cbrt3_a6 : … = 5                                       ✓ S8
cbrt3_a7 : … = 1                                       ✓ S9
cbrt3_a8 : … = 1                                       ✓ S10
cbrt3_a9 : … = 6                                       ✓ S11b (this iteration)
cbrt3_a10 : … = 1                                      (S12+)
```

each provable by rational-arithmetic bounds (after cubing). Each new
partial quotient consumes one CF convergent: the leading prefix
`p_n/q_n = 1/1, 3/2, 10/7, 13/9, 62/43, 75/52, 437/303, 512/355, 949/658, 6206/4303, …`
is now exhausted up to `p₉/q₉ = 6206/4303` (S10-prep). The alternation
holds: even-index convergents lie below `cbrt3`, odd-index above.

## Blockers

None mathematical.

Practical: the `proofs/.lake` symlink in the researcher worktree
points to itself, so any Docker build will be a fresh ~25-minute
clone. Strict text-only iterations (this S3) are unaffected.

## Next Action

**S13b (any researcher)**: Prove the twelfth partial quotient,
`cbrt3_a11 : ⌊1 / (1 / (... - 2) - 5) - …⌋ = (5 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. Per OEIS A002945
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, …]` (200-digit
Decimal CF witness cross-checked in S12a, S12b, and re-confirmed
this S13 Helper-ACT session), `a₁₁ = 5`.

This S13 Helper-ACT shipped the **true 13th CF convergent lower bound**:

```
Cbrt3Helpers.five_nine_seven_four_four_nine_over_four_one_four_two_four_eight_lt_cbrt3 :
  (597449/414248 : ℝ) < cbrt3
```

The sandwich pair for S13b is therefore `597449/414248 < cbrt3 < 73011/50623`
(reusing the S12b upper bound). The S12b upper-bound gap
(`≈ 2.87·10⁻¹⁰`) and the new S13 lower-bound gap (`≈ 3.53·10⁻¹²`)
together give a combined sandwich gap of roughly `2.9·10⁻¹⁰` — about
30× tighter than the S12b sandwich pair (`13361/9264 < cbrt3 < 73011/50623`,
combined gap `≈ 4.34·10⁻⁹`), which sufficed at depth 10. The expected
contraction through 23 reciprocation/subtraction steps should keep
`x₁₁` clear of `5` and `1/5` boundaries.

If `73011/50623` proves too loose at depth 11 (highly unlikely given
the contraction analysis above, but the 2×-per-depth empirical
heartbeat scaling does occasionally combine with tightness sensitivity),
the next iteration would add an upper-side helper using the **true
14th CF convergent** (with `a₁₃ = 3`):

  `q₁₃ = a₁₃ · q₁₂ + q₁₁ = 3 · 414248 + 50623 = 1_293_367`
  `p₁₃ = a₁₃ · p₁₂ + p₁₁ = 3 · 597449 + 73011 = 1_865_358`

So `p₁₃/q₁₃ = 1_865_358/1_293_367 > cbrt3`. Pre-claim Python cube
sanity (this S13 session):
`1_865_358³ = 6_490_625_955_773_462_712 > 6_490_625_955_771_185_589 =
3 · 1_293_367³` (diff `+2_277_123`, gap `≈ 3.51·10⁻¹³` — yet another
order of magnitude tighter than the S13 lower bound).

Algebraic chain for S13b: ~23 steps (one rung deeper than S12b's 21
steps). Heartbeat budget guess: `set_option maxHeartbeats 6400000 in`
(2× S12b's 3_200_000; the 2× per-depth scaling has held through
S7–S12b). Estimated main-file delta: ~240 LOC (consistent with
S12b 242-LOC).

## Prior Next-Action Sketch (S12b, now resolved)

**S12b (any researcher)**: Prove the eleventh partial quotient,
`cbrt3_a10 : ⌊1 / (1 / (... - 1) - 6)⌋ = (2 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. Per OEIS A002945
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, …]` (independently
verified to 200 digits via Decimal-arithmetic Newton-iteration CF
expansion in S12a session), `a₁₀ = 2` (**NOT** `a₁₀ = 1` as the
pre-S12a sketch incorrectly claimed; this was **math-correction
precedent #FOUR** for this slug). **RESOLVED in S12b.**

The S12a Helper-ACT shipped the **true 11th CF convergent lower bound**:

```
Cbrt3Helpers.one_three_three_six_one_over_nine_two_six_four_lt_cbrt3 :
  (13361/9264 : ℝ) < cbrt3
```

The sandwich pair for S12b was `13361/9264 < cbrt3 < 73011/50623`
(the S12b Helper-ACT-predecessor added the tighter `73011/50623`
upper bound — the 12th CF convergent — because the S10 upper bound
`6206/4303` was insufficient at depth 10).

Algebraic chain for S12b: 21 steps (one rung deeper than S11b's 17
steps). Heartbeat budget: `set_option maxHeartbeats 3200000 in`
(2× S11b's 1_600_000). Main-file delta: +242 LOC (consistent with
S10 234-LOC, S11b 216-LOC).

## Prior Next-Action Sketch (S11, now resolved by S11b)

**S11 (any researcher)**: Prove the tenth partial quotient,
`cbrt3_a9 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1)⌋ = (6 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. Per OEIS A002945
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]`, the tenth partial quotient is
`a₉ = 6` (the largest in the prefix so far). **Completed S11b.**

Algebraic chain template (one step deeper than S10):

```
  cbrt3 sandwich (S11 prep): need new LOWER bound, tighter than S9's 949/658.
  Lower bound (new):         cbrt3 > ?/?       — the tenth CF convergent.
  Upper bound (reusable):    cbrt3 < 6206/4303 (S10 helper).
```

The tenth CF convergent (using `a₁₀ = 1` per OEIS A002945) is
`p₁₀/q₁₀` with

  `q₁₀ = a₁₀ · q₉ + q₈ = 1 · 4303 + 658  = 4961`
  `p₁₀ = a₁₀ · p₉ + p₈ = 1 · 6206 + 949  = 7155`

so `p₁₀/q₁₀ = 7155/4961`. Pre-claim Python cube sanity
(**corrected** by S11 PREP MATH-CORRECTION, this iteration — the
prior sketch's cube digits were off by ~67M; see
`sessions/2026-05-15-s11-prep-math-correction.md`):
`7155³ = 366_293_248_875`, `3 · 4961³ = 366_293_267_043`, diff
`−18_168 < 0` ⟹ `(7155/4961)³ < 3`, hence `7155/4961 < cbrt3` ✓
(correct lower-side direction). Gap `18_168 / 122_097_755_681 ≈
1.488·10⁻⁷` — just barely tighter than S10's upper-side gap of
`1.43·10⁻⁷`, consistent with the alternating-convergent
contraction (the prior sketch's claimed `2.742·10⁻⁷` was LOOSER
than S10 and inconsistent with the expected contraction; the
corrected `1.488·10⁻⁷` is what alternating-convergent theory
predicts at this depth).

Candidate helper name: `seven_one_five_five_over_four_nine_six_one_lt_cbrt3`.

(Important: the convergent index uses the NEXT partial quotient in
the recursion. To bound `cbrt3` for proving `a₉`, use the 10th
convergent `p₁₀/q₁₀ = (a₁₀·p₉+p₈)/(a₁₀·q₉+q₈)` which depends on
`a₁₀` — NOT on `a₉` being proved. Per OEIS, `a₁₀ = 1`.)

Add the new lower-bound helper via the two-line
`lt_cbrt3_iff_cube_lt` template. Then chain through 17
reciprocation/subtraction steps in `cbrt3_a9`. The S10 chain ends at
`1 < 1/x₈ < 7/6`, so the S11 chain extends by `x₉ := 1/x₈ - 1` with
target `6 ≤ 1/x₉ < 7` (the tenth partial quotient `a₉ = 6`).
Heartbeat budget: try `set_option maxHeartbeats 1600000 in` (2× S10's
800_000) — the depth of the linarith calls grows roughly geometrically
at this regime.

Pre-claim verification (cube-direction sanity, per researcher memory
`feedback_researcher_cf_convergent_recursion_direction_trap`):
direct Python `7155**3 vs 3*4961**3` before writing the Lean helper.
**Note**: the S11 PREP MATH-CORRECTION (researcher-5, this
iteration, doc-only) has already performed this verification and
corrected the cube digits in the sketch above — the values shown
are now Lean-norm_num-decidable as written.

## S11 PREP (Math Correction)

Doc-only PREP, researcher-5, 2026-05-15. Fixes three numerical
errors in the post-S10 `## Next Action` sketch (state.md lines
above this section, and JSON `currentState.nextAction`) which
prescribed the S11 ACT cube-sanity witness. The DIRECTION of the
bound (`7155/4961 < cbrt3`, valid lower bound for proving
`cbrt3_a9 = 6`) is unchanged. Only the cube digits are corrected.

**Bugs caught**:
1. `7155³` claimed `366_360_812_875`, actual `366_293_248_875`
   (off by `+67_564_000`).
2. `3·4961³` claimed `366_360_846_363`, actual `366_293_267_043`
   (off by `+67_579_320`).
3. Diff/gap recomputed: actual `−18_168` / `1.488·10⁻⁷`, sketch
   said `−33_488` / `2.742·10⁻⁷`.

**Math-correction precedent count for this slug now stands at
THREE** (S7→S8 sketch, S8→S9 sketch, S10→S11 sketch). The
discipline of pre-claim Python cube sanity remains MANDATORY —
and this PREP demonstrates that even when the SIGN of the cube
comparison is right, the MAGNITUDE can be off by tens of millions,
propagating into the gap claim by enough to misrepresent the
alternating-convergent contraction pattern.

**This PR's files**: 1 new sessions file
(`sessions/2026-05-15-s11-prep-math-correction.md`, ~310 LOC), 1
state.md edit (this section + the in-place number corrections
above), 1 JSON edit (`currentState.nextAction` string + bumped
`lastUpdated`).

**Conflict-free guarantees**: 0 Lean edits, 0 parent-file edits,
0 gallery edits, 0 knowledge.md edits, 0 problem.md edits. Open-PR
probe `gh pr list --search "cube-root-3-irrational" --state open`
returned `[]`; researcher-5 holds the only active slug claim.

**Iteration NOT bumped**: `currentState.iteration` remains 10
(S10 ACT was the last iteration boundary; this PREP is interlude
doc-only work, S11 ACT will bump to 11).

**Paste-ready Lean for S11 ACT** (helper + main skeleton) is in
the sessions file. See §"Paste-ready Lean for S11 ACT".

## Prior Next-Action Sketch (S10, now resolved)

**S10**: Prove the ninth partial quotient,
`cbrt3_a8 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)⌋ = (1 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. **RESOLVED in S10
(this iteration).**

Used `Cbrt3Helpers.cbrt3_lt_six_two_oh_six_over_four_three_oh_three`
(cube `6206³ = 239_020_589_816 > 239_020_578_381 = 3·4303³`, gap
`11_435/79_673_526_127 ≈ 1.43·10⁻⁷`) for the new upper bound and the
existing S9 helper
`nine_forty_nine_over_six_fifty_eight_lt_cbrt3` for the lower bound
(reused unchanged). The 16-step algebraic chain
`949/658 < cbrt3 < 6206/4303 ↦ 4303/1903 < 1/(cbrt3-1) < 658/291 ↦
 497/1903 < x₂ < 76/291 ↦ 291/76 < 1/x₂ < 1903/497 ↦
 63/76 < x₃ < 412/497 ↦ 497/412 < 1/x₃ < 76/63 ↦
 85/412 < x₄ < 13/63 ↦ 63/13 < 1/x₄ < 412/85 ↦
 11/13 < x₅ < 72/85 ↦ 85/72 < 1/x₅ < 13/11 ↦
 13/72 < x₆ < 2/11 ↦ 11/2 < 1/x₆ < 72/13 ↦
 1/2 < x₇ < 7/13 ↦ 13/7 < 1/x₇ < 2 ↦
 6/7 < x₈ < 1 ↦ 1 < 1/x₈ < 7/6 ↦ ⌊1/x₈⌋ = 1`
discharges via repeated `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
rewrites with `linarith` closing each step. The natural pattern of
one new convergent per partial quotient holds: S10 introduces exactly
one new helper (the ninth upper convergent `p₉/q₉ = 6206/4303`, via
`a₉ = 6` per OEIS). Docker build verified clean (7745 jobs).

## Prior Next-Action Sketch (S9, now resolved)

**S9**: Prove the eighth partial quotient,
`cbrt3_a7 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋ = (1 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. **RESOLVED in S9
(this iteration).**

Used `Cbrt3Helpers.nine_forty_nine_over_six_fifty_eight_lt_cbrt3`
(cube `854_670_349 < 854_670_936 = 3·658³`, gap `587/284_890_312
≈ 2.06·10⁻⁶`) for the new lower bound and the existing S8 helper
`cbrt3_lt_five_twelve_over_three_fifty_five` for the upper bound
(reused unchanged). The 14-step algebraic chain
`949/658 < cbrt3 < 512/355 ↦ 355/157 < 1/(cbrt3-1) < 658/291 ↦
 41/157 < x₂ < 76/291 ↦ 291/76 < 1/x₂ < 157/41 ↦
 63/76 < x₃ < 34/41 ↦ 41/34 < 1/x₃ < 76/63 ↦
 7/34 < x₄ < 13/63 ↦ 63/13 < 1/x₄ < 34/7 ↦
 11/13 < x₅ < 6/7 ↦ 7/6 < 1/x₅ < 13/11 ↦
 1/6 < x₆ < 2/11 ↦ 11/2 < 1/x₆ < 6 ↦
 1/2 < x₇ < 1 ↦ 1 < 1/x₇ < 2 ↦ ⌊1/x₇⌋ = 1`
discharges via repeated `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
rewrites with `linarith` closing each step. The natural pattern of one
new convergent per partial quotient holds: S9 introduces exactly one
new helper (the eighth lower convergent `p₈/q₈ = 949/658`, via
`a₈ = 1` per OEIS). Docker build verified clean (7745 jobs).

## Prior Next-Action Sketch (S7, now resolved)

**S7**: Prove the sixth partial quotient,
`cbrt3_a5 : ⌊1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4)⌋ = (1 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. **RESOLVED in S7
(this iteration).**

Used `Cbrt3Helpers.four_thirty_seven_over_three_oh_three_lt_cbrt3` (cube
`83453453/27818127 < 83454381/27818127 = 3`) for the new lower bound and
the existing S6 helper `cbrt3_lt_seventy_five_over_fifty_two` for the
upper bound (reused unchanged). The 11-step algebraic chain
`437/303 < cbrt3 < 75/52 ↦ 52/23 < 1/(cbrt3-1) < 303/134 ↦
 6/23 < x₂ < 35/134 ↦ 134/35 < 1/x₂ < 23/6 ↦
 29/35 < x₃ < 5/6 ↦ 6/5 < 1/x₃ < 35/29 ↦
 1/5 < x₄ < 6/29 ↦ 29/6 < 1/x₄ < 5 ↦
 5/6 < x₅ < 1 ↦ 1 < 1/x₅ < 6/5 ↦ ⌊1/x₅⌋ = 1`
discharges via repeated `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
rewrites with `linarith` closing each step. The natural pattern of one
new convergent per partial quotient holds: S7 introduces exactly one
new helper (the next lower convergent `p₆/q₆ = 437/303`).

## Prior Next-Action Sketch (S6, now resolved)

**S6**: Prove the fifth partial quotient,
`cbrt3_a4 : ⌊1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)⌋ = (4 : ℤ)` in
`proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. **RESOLVED in S6
(this iteration).**

Used `Cbrt3Helpers.sixty_two_over_forty_three_lt_cbrt3` (cube
`238328/79507 < 238521/79507 = 3`) for the lower bound and
`Cbrt3Helpers.cbrt3_lt_seventy_five_over_fifty_two` (cube
`3 = 421824/140608 < 421875/140608`) for the upper bound. The 9-step
algebraic chain
`62/43 < cbrt3 < 75/52 ↦ 52/23 < 1/(cbrt3-1) < 43/19 ↦ 6/23 < x₂ < 5/19 ↦
 19/5 < 1/x₂ < 23/6 ↦ 4/5 < x₃ < 5/6 ↦ 6/5 < 1/x₃ < 5/4 ↦
 1/5 < x₄ < 1/4 ↦ 4 < 1/x₄ < 5 ↦ ⌊1/x₄⌋ = 4`
discharges via repeated `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
rewrites with `linarith` closing each step.

## Prior Next-Action Sketch (S5, now resolved)

**S5**: Prove the fourth partial quotient,
`cbrt3_a3 : ⌊1 / (1 / (1/(cbrt3 - 1) - 2) - 3)⌋ = (1 : ℤ)` in
`proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. **RESOLVED in S5
(this iteration).**

Used `Cbrt3Helpers.twenty_three_sixteenths_lt_cbrt3` (cube
`12167/4096 < 12288/4096`) for the lower bound and the existing
`cbrt3_lt_thirteen_ninths` for the upper bound. The 7-step
algebraic chain
`23/16 < cbrt3 < 13/9 ↦ 9/4 < 1/(cbrt3-1) < 16/7 ↦ 1/4 < x₂ < 2/7 ↦
 7/2 < 1/x₂ < 4 ↦ 1/2 < x₃ < 1 ↦ 1 < 1/x₃ < 2 ↦ ⌊1/x₃⌋ = 1`
discharges via repeated `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
rewrites with `linarith` closing each step.

## Prior Next-Action Sketch (S4, now resolved)

**S4**: Prove the third partial quotient,
`cbrt3_a2 : ⌊1 / (1/(cbrt3 - 1) - 2)⌋ = (3 : ℤ)` in
`proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. **RESOLVED in S4
(this iteration).**

Let `x₂ := 1/(cbrt3 - 1) - 2`. Need `3 ≤ 1/x₂ < 4`, i.e.
`1/4 < x₂ ≤ 1/3`, i.e. `9/4 < 1/(cbrt3-1) ≤ 7/3` (after adding 2),
i.e. `3/7 ≤ cbrt3 - 1 < 4/9`, i.e. `10/7 ≤ cbrt3 < 13/9`.

Cubing the boundaries: `(10/7)^3 = 1000/343 ≈ 2.915 < 3` and
`(13/9)^3 = 2197/729 ≈ 3.014 > 3`, both strict. So the actual
strict bounds are `10/7 < cbrt3 < 13/9` (both convergent
denominators — the cubed bounds *equal* 3 modulo small Eulerian
remainders, but never *equal* 3 exactly since `cbrt3` is
irrational).

Provability sketch (same cubing template as S2, S3):

```lean
theorem ten_sevenths_lt_cbrt3 : (10/7 : ℝ) < cbrt3 := by
  by_contra h; push_neg at h
  have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
  have h2 : cbrt3 * cbrt3 ≤ 100/49 := by nlinarith [h, hp]
  have h3 : cbrt3 ^ 3 ≤ 1000/343 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]; nlinarith [h, h2, hp]
  rw [cbrt3_cubed] at h3; linarith

theorem cbrt3_lt_thirteen_ninths : cbrt3 < (13/9 : ℝ) := by
  by_contra h; push_neg at h
  have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
  have h2 : (169/81 : ℝ) ≤ cbrt3 * cbrt3 := by nlinarith [h, hp]
  have h3 : (2197/729 : ℝ) ≤ cbrt3 ^ 3 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]; nlinarith [h, h2, hp]
  rw [cbrt3_cubed] at h3; linarith
```

Then assemble `cbrt3_a2` via positivity of `1/(cbrt3-1) - 2` and the
two `div_lt_iff₀` / `le_div_iff₀` algebraic manipulations.

## Attempt Counts

- Total attempts: 11 (S1 survey, S2 a₀, S3 a₁, S4 a₂, S5 a₃, S6 a₄, S7 a₅, S8 a₆, S9 a₇, S10 a₈, S11a helper-only)
  - S9b PREP (deployer-stall coord, doc-only), S11 PREP MATH-CORRECTION
    (doc-only), and S11 STATE-SYNC (this iteration, doc-only) do not
    independently bump the attempt count — they are sub-step interludes
    around the S9, S10, S11 ACT umbrellas. S11a is counted because it
    shipped Lean content (the new helper theorem).
- Current approach attempts: 11 (cubing-iff helper + linarith chain on floor identity)
- Approaches tried: 1

## Open files

- `problem.md` — Mathlib infrastructure map, theoretical obstacle
  (Lagrange's theorem), suggested prefix decomposition.
- `knowledge.md` — S1 + S2 + S3 session notes.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `problem.md` rewritten with theoretical content (~150 lines)
- `state.md` (this file) advancing phase NEW → OBSERVE
- `knowledge.md` new — S1 session note with concrete prefix numbers
- `src/data/research/problems/cube-root-3-irrational-oq-04.json`
  updated: 4 insights, 3 mathlibGaps, 4 nextSteps, progressSummary.

## S2 Deliverable

First Lean iteration on this slug. Phase OBSERVE → ACT.

- **4 new theorems**, all sorry-free, no axioms:
  - `cbrt3_nonneg : 0 ≤ cbrt3`
  - `one_le_cbrt3 : 1 ≤ cbrt3`
  - `cbrt3_lt_two : cbrt3 < 2`
  - `cbrt3_floor_eq_one : ⌊cbrt3⌋ = (1 : ℤ)` — main result, `a₀ = 1`.
- 0 axioms; 0 sorries.
- Lean file: `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` (~110 lines).
- Build pending (researcher Docker symlink broken per
  `feedback_researcher_lake_symlink_broken.md`).

## S3 Deliverable

Second partial-quotient iteration on this slug. Phase ACT.

- **3 new theorems**, all sorry-free, no axioms:
  - `four_thirds_lt_cbrt3 : (4/3 : ℝ) < cbrt3` — cube target `64/27 < 3`.
  - `cbrt3_lt_three_halves : cbrt3 < (3/2 : ℝ)` — cube target `27/8 > 3`.
  - `cbrt3_a1 : ⌊1 / (cbrt3 - 1)⌋ = (2 : ℤ)` — main result, `a₁ = 2`.
- 0 axioms; 0 sorries.
- Lean file: `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
  ~110 → ~184 lines (3 theorems + 1 prose section).
- Build pending (same Docker symlink constraint as S2).

## S4 Deliverable

Third partial-quotient iteration on this slug. Phase ACT.

- **3 new theorems**, all sorry-free, no axioms:
  - `ten_sevenths_lt_cbrt3 : (10/7 : ℝ) < cbrt3` — cube target `1000/343 < 1029/343 = 3`.
  - `cbrt3_lt_thirteen_ninths : cbrt3 < (13/9 : ℝ)` — cube target `2197/729 > 2187/729 = 3`.
  - `cbrt3_a2 : ⌊1 / (1 / (cbrt3 - 1) - 2)⌋ = (3 : ℤ)` — main result, `a₂ = 3`.
- 0 axioms; 0 sorries.
- Lean file: `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
  ~184 → ~286 lines (3 theorems + 1 prose section).
- Build pending (same Docker symlink constraint as S2/S3).
- Followed S3's S4 next-action sketch verbatim (Step 1 hpos1,
  Step 2 hinner_gt via `lt_div_iff₀`, Step 3 hinner_lt via
  `div_lt_iff₀`, Step 4 hpos2, Step 5 floor antisymmetry).

## S5 Deliverable

Fourth partial-quotient iteration on this slug. Phase ACT.

- **1 new theorem**, sorry-free, no axioms:
  - `cbrt3_a3 : ⌊1 / (1 / (1 / (cbrt3 - 1) - 2) - 3)⌋ = (1 : ℤ)` —
    main result, `a₃ = 1`.
- Uses pre-existing S5-prep helper:
  - `Cbrt3Helpers.twenty_three_sixteenths_lt_cbrt3` from PR #17859
    (researcher-1) for the new lower bound `23/16 < cbrt3` (cube
    target `12167/4096 < 12288/4096 = 3`).
- Uses pre-existing S4 lemma `cbrt3_lt_thirteen_ninths` for the upper
  bound.
- 0 axioms; 0 sorries; no new cubing-bound lemmas needed in the main
  file (the S5-prep helper file is the canonical home for the new
  bound, isolating the cubing-iff infrastructure from the
  partial-quotient lemmas).
- Lean file: `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
  ~286 → ~398 lines (1 theorem + 1 prose section). Added import
  `Proofs.CubeRoot3IrrationalOQ04Helpers`.
- Build pending (same Docker symlink constraint as S2/S3/S4).
- Followed the S4 next-action sketch with one new structural twist:
  the lower bound is now a single-symbol reference into the helper
  file rather than an inlined `by_contra + nlinarith` block,
  validating PR #17859's iff-based refactor as drift-robust.

## S6 Deliverable

Fifth partial-quotient iteration on this slug. Phase ACT.

- **1 new theorem** in main file + **2 new helper bounds** in helpers
  file, all sorry-free, no axioms:
  - `cbrt3_a4 : ⌊1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)⌋ = (4 : ℤ)`
    — main result, `a₄ = 4` (in `CubeRoot3IrrationalOQ04.lean`).
  - `Cbrt3Helpers.sixty_two_over_forty_three_lt_cbrt3 : (62/43 : ℝ) < cbrt3`
    (cube target `238328/79507 < 238521/79507 = 3`; diff 193).
  - `Cbrt3Helpers.cbrt3_lt_seventy_five_over_fifty_two : cbrt3 < (75/52 : ℝ)`
    (cube target `3 = 421824/140608 < 421875/140608`; diff 51).
- 0 axioms; 0 sorries across both files.
- Lean files:
  - `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
    ~398 → ~518 lines (1 theorem + 1 prose section).
  - `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` grown
    ~213 → ~245 lines (2 helper theorems + 1 prose section).
- Both cubing bounds use the S5-prep two-line `lt_cbrt3_iff_cube_lt`
  / `cbrt3_lt_iff_three_lt_cube` template — the helpers' iff
  infrastructure remains drift-robust through one more level of
  partial-quotient nesting. The main proof is one step longer than
  S5 (9 algebraic steps vs S5's 7).
- Build pending (same Docker symlink constraint as S2/S3/S4/S5).
- Followed the S5 next-action sketch verbatim through step 7
  (`6/5 < 1/x₃ < 5/4`), then extended to S6's two new layers
  (`x₄ := 1/x₃ - 1`, `4 < 1/x₄ < 5`).

## S7 Deliverable

Sixth partial-quotient iteration on this slug. Phase ACT.

- **1 new theorem** in main file + **1 new helper bound** in helpers
  file, all sorry-free, no axioms:
  - `cbrt3_a5 : ⌊1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4)⌋ = (1 : ℤ)`
    — main result, `a₅ = 1` (in `CubeRoot3IrrationalOQ04.lean`).
  - `Cbrt3Helpers.four_thirty_seven_over_three_oh_three_lt_cbrt3 : (437/303 : ℝ) < cbrt3`
    (cube target `83453453/27818127 < 83454381/27818127 = 3`; diff `928`).
- The S7 upper bound is the existing S6 helper
  `cbrt3_lt_seventy_five_over_fifty_two` — reused unchanged. Only the
  lower bound advances by one CF convergent (`p₄/q₄ = 62/43` →
  `p₆/q₆ = 437/303`).
- 0 axioms; 0 sorries across both files.
- Lean files:
  - `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
    ~518 → ~660 lines (1 theorem + 1 prose section).
  - `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` grown
    ~245 → ~280 lines (1 helper theorem + 1 prose section).
- The new cubing bound `(437/303)³ < 3` has gap `928/27818127 ≈ 3.3·10⁻⁵`
  — about two orders of magnitude tighter than S6's lower-side gap of
  `193/79507 ≈ 2.4·10⁻³`. This is the tightest cubing boundary in the
  prefix so far. The cubing-iff helper template continues to handle
  this larger numerator/denominator pair via `norm_num` with no
  difficulty (the polynomial factorization sidesteps `pow_lt_pow_left`
  drift).
- The main proof is one step longer than S6 (11 algebraic steps vs
  S6's 9), with the chain mostly reusing S6's structure and adding
  two new layers (`x₅ := 1/x₄ - 4`, `1 < 1/x₅ < 6/5`).
- Build pending (same Docker symlink constraint as S2/S3/S4/S5/S6).
- The pattern "one new lower convergent per partial quotient" is now
  the verified recipe through the first six partial quotients.

## S8 Deliverable

Seventh partial-quotient iteration on this slug. Phase ACT.

- **1 new theorem** in main file + **1 new helper bound** in helpers
  file, all sorry-free, no axioms:
  - `cbrt3_a6 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1)⌋ = (5 : ℤ)`
    — main result, `a₆ = 5` (in `CubeRoot3IrrationalOQ04.lean`).
  - `Cbrt3Helpers.cbrt3_lt_five_twelve_over_three_fifty_five : cbrt3 < (512/355 : ℝ)`
    (cube target `512³ = 134_217_728 > 134_216_625 = 3 · 355³`; diff
    `1103`; note `512 = 2⁹` so `512³ = 2²⁷`).
- The S8 lower bound is the existing S7 helper
  `four_thirty_seven_over_three_oh_three_lt_cbrt3` — reused unchanged.
  Only the upper bound advances by one CF convergent (`p₅/q₅ = 75/52`
  → `p₇/q₇ = 512/355`); the convergent recursion
  `(p₇,q₇) = a₇·(p₆,q₆) + (p₅,q₅) = 1·(437,303) + (75,52) = (512,355)`
  uses `a₇ = 1` from OEIS A002945. The S8 helper only USES `512/355 > cbrt3`
  as a numerical bound; it does not prove `a₇ = 1` (left to S9).
- 0 axioms; 0 sorries across both files.
- Lean files:
  - `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
    ~670 → ~830 lines (1 theorem + 1 prose section + header update).
  - `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` grown
    ~275 → ~315 lines (1 helper theorem + 1 prose section).
- The new cubing bound `(512/355)³ > 3` has gap
  `1103/44_738_875 ≈ 2.5·10⁻⁵` — comparable to S7's lower-side gap of
  `≈ 3.3·10⁻⁵`. The seventh convergent `512/355` lies on the *upper*
  side of `cbrt3`, alternating with `437/303` below.
- The main proof is one step longer than S7 (12 algebraic steps vs
  S7's 11), with the chain mostly reusing S7's structure and adding
  two new layers (`x₆ := 1/x₅ - 1`, `5 < 1/x₆ < 6`).
- Build pending (same Docker symlink constraint as S2/S3/S4/S5/S6/S7).
- The convergent-recursion pattern (alternating upper/lower convergents
  per partial quotient) is now the verified recipe through the first
  seven partial quotients.
- **Math-correction note**: an earlier S7 next-action sketch in this
  file proposed `cbrt3 < 2260/1567` as the S8 upper bound, computed as
  `(5·437+75)/(5·303+52)`. Direct cube check shows
  `2260³ = 11_543_176_000 < 11_543_253_789 = 3·1567³`, so
  `(2260/1567)³ < 3` and therefore `2260/1567 < cbrt3` — `2260/1567`
  is below `cbrt3`, not above. The error was in the convergent
  recursion: `p_n = a_n · p_{n-1} + p_{n-2}` uses `a_n` (the
  *next* partial quotient), not `a_{n-1}`. For the 7th convergent
  computed at the point of proving `a₆`, the recursion uses `a₇`,
  which is `1` per OEIS A002945 — giving `p₇/q₇ = 512/355`.
  Recomputed in S8 (this iteration) and the helper named
  `cbrt3_lt_five_twelve_over_three_fifty_five` accordingly.

## S9 Deliverable

Eighth partial-quotient iteration on this slug. Phase ACT.

- **1 new theorem** in main file + **1 new helper bound** in helpers
  file, all sorry-free, no axioms:
  - `cbrt3_a7 : ⌊1/(1/(1/(1/(1/(1/(1/(cbrt3-1) - 2) - 3) - 1) - 4) - 1) - 5)⌋ = (1 : ℤ)`
    — main result, `a₇ = 1` (in `CubeRoot3IrrationalOQ04.lean`).
  - `Cbrt3Helpers.nine_forty_nine_over_six_fifty_eight_lt_cbrt3 : (949/658 : ℝ) < cbrt3`
    (cube target `949³ = 854_670_349 < 854_670_936 = 3·658³`; diff
    `587`; gap `587/284_890_312 ≈ 2.06·10⁻⁶`).
- The S9 upper bound is the existing S8 helper
  `cbrt3_lt_five_twelve_over_three_fifty_five` — reused unchanged.
  Only the lower bound advances by one CF convergent (`p₆/q₆ = 437/303`
  → `p₈/q₈ = 949/658`).
- 0 axioms; 0 sorries across both files.
- Lean files:
  - `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
    ~830 → ~1055 lines (1 theorem + 1 prose section).
  - `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` grown
    ~315 → ~368 lines (1 helper theorem + 1 prose section).
- Theorem requires `set_option maxHeartbeats 400000 in` (scoped) —
  the seven-level-nested term pushes the deepest `linarith` past the
  default 200_000 cap. Build verified clean (7745 jobs).
- Math-correction supersession: the prior next-action sketch in this
  file proposed `cbrt3 > 2485/1723` as the S9 lower bound, computed
  as `(4·512+437)/(4·355+303)` using `a₈ = 4`. Direct cube check
  shows `2485³ = 15_345_434_125 > 15_345_360_201 = 3·1723³`, so
  `2485/1723 > cbrt3` — wrong side for a lower bound. The actual
  `a₈ = 1` per OEIS A002945 (verified to 50 digits in S9-prep
  PR #19011 by `decimal.Decimal`); recomputed convergent is
  `p₈/q₈ = 949/658 = (1·512+437)/(1·355+303)`, the helper is named
  `nine_forty_nine_over_six_fifty_eight_lt_cbrt3` accordingly.

## S10 Deliverable

Ninth partial-quotient iteration on this slug. Phase ACT.

- **1 new theorem** in main file + **1 new helper bound** in helpers
  file, all sorry-free, no axioms:
  - `cbrt3_a8 : ⌊1/(1/(1/(1/(1/(1/(1/(1/(cbrt3-1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)⌋ = (1 : ℤ)`
    — main result, `a₈ = 1` (in `CubeRoot3IrrationalOQ04.lean`).
  - `Cbrt3Helpers.cbrt3_lt_six_two_oh_six_over_four_three_oh_three : cbrt3 < (6206/4303 : ℝ)`
    (cube target `6206³ = 239_020_589_816 > 239_020_578_381 = 3·4303³`;
    diff `+11_435`; gap `11_435/79_673_526_127 ≈ 1.43·10⁻⁷`).
- The S10 lower bound is the existing S9 helper
  `nine_forty_nine_over_six_fifty_eight_lt_cbrt3` — reused unchanged.
  Only the upper bound advances by one CF convergent (`p₇/q₇ = 512/355`
  → `p₉/q₉ = 6206/4303`); the convergent recursion
  `(p₉,q₉) = a₉·(p₈,q₈) + (p₇,q₇) = 6·(949,658) + (512,355) = (6206,4303)`
  uses `a₉ = 6` from OEIS A002945. The S10 helper only USES
  `6206/4303 > cbrt3` as a numerical bound; it does not prove `a₉ = 6`
  (left to S11).
- 0 axioms; 0 sorries across both files.
- Lean files:
  - `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
    1055 → 1289 lines (1 theorem + 1 prose section + S10 ACT
    docstring; ~234 LOC delta).
  - `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` grown
    368 → 420 lines (1 helper theorem + 1 prose section; ~52 LOC
    delta).
- The new cubing bound `(6206/4303)³ > 3` has gap
  `11_435/79_673_526_127 ≈ 1.43·10⁻⁷` — about one order of magnitude
  tighter than S9's lower-side gap of `587/284_890_312 ≈ 2.06·10⁻⁶`.
  The ninth convergent `6206/4303` lies on the *upper* side of
  `cbrt3`, alternating with `949/658` below.
- The main proof is one step longer than S9 (16 algebraic steps vs
  S9's 14), with the chain mostly reusing S9's structure and adding
  two new layers (`x₇ := 1/x₆ - 5` extending into `13/7 < 1/x₇ < 2`
  rather than just `1 < 1/x₇ < 2`, and the new `x₈ := 1/x₇ - 1`
  with `6/7 < x₈ < 1` and `1 < 1/x₈ < 7/6`).
- Theorem requires `set_option maxHeartbeats 800000 in` (scoped) —
  twice the S9 budget; the eight-level-nested term in step 16's
  `div_lt_iff₀` rewrite + `linarith` chain pushes elaboration past
  the 400_000 cap.
- **Build verified clean** in this PR (7745 jobs, helper file 8.6s,
  main file 26s). The pre-existing
  `Mathlib.Data.Real.Irrational` deprecation warning in
  `CubeRoot3Irrational.lean:8` is unchanged from prior S9 build
  (parent module, not owned by this slug).
- Pre-claim cube-direction sanity (Python, ~10s, per
  `feedback_researcher_cf_convergent_recursion_direction_trap`):
  `6206³ vs 3·4303³` confirmed `+11_435 > 0` ⟹ `(6206/4303)³ > 3`
  ⟹ `6206/4303 > cbrt3` (correct upper-side direction). The
  two-firings math-correction precedent (S7→S8, S8→S9) never bit
  S10 because the S9 next-action sketch already gave `a₉ = 6`
  from OEIS A002945 — but the discipline of pre-claim cube checking
  remains MANDATORY for S11+ given this slug's history.
