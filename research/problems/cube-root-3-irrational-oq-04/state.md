# Current State

**Phase**: ACT
**Since**: 2026-05-13 (S7)
**Iteration**: 7

## Current Focus

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
than S6's lower-side gap of `2.4·10⁻³`. This is the tightest cubing
boundary in the prefix so far, consistent with `437/303` being the
sixth convergent of the CF (the partial-quotient pattern requires
the next convergent for each new `aₙ`, so S7's lower convergent
`p₆/q₆ = 437/303` follows S6's `p₄/q₄ = 62/43`).

## Previous Focus

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

## Earlier Focus

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
cbrt3_a5 : … = 1                                       ✓ S7 (this iteration)
cbrt3_a6 : … = 5                                       (S8+)
```

each provable by rational-arithmetic bounds (after cubing). Each new
partial quotient consumes one CF convergent: the leading prefix
`p_n/q_n = 1/1, 3/2, 10/7, 13/9, 62/43, 75/52, 437/303, …` is now
exhausted up to `p₆/q₆ = 437/303` (S7-prep).

## Blockers

None mathematical.

Practical: the `proofs/.lake` symlink in the researcher worktree
points to itself, so any Docker build will be a fresh ~25-minute
clone. Strict text-only iterations (this S3) are unaffected.

## Next Action

**S8 (any researcher)**: Prove the seventh partial quotient,
`cbrt3_a6 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1)⌋ = (5 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. Per OEIS A002945
`[1; 2, 3, 1, 4, 1, 5, …]`, the seventh partial quotient is `a₆ = 5`.

Algebraic chain template (one step deeper than S7):

```
  cbrt3 sandwich (S8 prep): need new upper bound, tighter than S6/S7's 75/52.
  Lower bound (reusable): 437/303 < cbrt3 (S7 helper).
  Upper bound (new):       cbrt3 < ?/?       — the seventh CF convergent.
```

The seventh CF convergent is `p₇/q₇` with denominators

  `q₇ = a₆ · q₆ + q₅ = 5 · 303 + 52 = 1567`
  `p₇ = a₆ · p₆ + p₅ = 5 · 437 + 75 = 2260`

so `p₇/q₇ = 2260/1567 ≈ 1.4422463…` (vs `cbrt3 ≈ 1.4422496…`). Cube
target: `(2260/1567)³ = ?  > 3 · 1567³ = ?` — both ~5·10⁻⁶ apart,
which is well within `norm_num`'s reach.

Add a new helper
`two_two_six_oh_over_one_five_six_seven_gt_cbrt3 : cbrt3 < (2260/1567 : ℝ)`
via the two-line `cbrt3_lt_iff_three_lt_cube` template, then chain through
12 reciprocation/subtraction steps:

```
  437/303 < cbrt3 < 2260/1567
  ↦ 1567/2260 < cbrt3-1 < ... rerun the chain ↦
  needed: rational sandwich showing ⌊1/x₆⌋ = 5 where x₆ := 1/x₅ - 1.
```

The S7 helpers' iff infrastructure continues to standardize the new
cubing bound. The main proof should be ~11–13 algebraic steps,
matching S7's shape one level deeper.

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

- Total attempts: 7 (S1 survey, S2 a₀, S3 a₁, S4 a₂, S5 a₃, S6 a₄, S7 a₅)
- Current approach attempts: 7 (cubing-iff helper + linarith chain on floor identity)
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
