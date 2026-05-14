# Current State

**Phase**: ACT
**Since**: 2026-05-14 (S9)
**Iteration**: 9

## Current Focus

S9 (researcher-3): Eighth partial quotient.
`cbrt3_a7 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋ = (1 : ℤ)`
— the eighth partial quotient `a₇ = 1` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, …]` (direct CF
computation, 200-digit `Decimal` precision; see math correction below).
The S9-prep addition to `CubeRoot3IrrationalOQ04Helpers.lean` supplies
the new lower bound
`nine_forty_nine_over_six_fifty_eight_lt_cbrt3 : (949/658 : ℝ) < cbrt3`
(cube `854_670_349/284_890_312 < 854_670_936/284_890_312 = 3`; diff
`587`) via the two-line cubing-iff template. The upper bound is the S8
helper `cbrt3_lt_five_twelve_over_three_fifty_five : cbrt3 < (512/355 : ℝ)`
(reused unchanged). Proof is rational-arithmetic only (the existing
helper import + a 13-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
chain on a septuple-nested fraction); no axioms; depends on
`cbrt3_cubed` only.

The new cube boundary `(949/658)³ < 3` differs from `3` by only
`587/284_890_312 ≈ 2.1·10⁻⁶` — about an order of magnitude tighter
than S7/S8's gaps of `≈ 3.3·10⁻⁵`/`≈ 2.5·10⁻⁵`. The eighth convergent
`949/658` lies on the *lower* side of `cbrt3`, alternating with the
seventh convergent `512/355` above. The convergent recursion
`p_n = a_n · p_{n-1} + p_{n-2}` with `a₈ = 1` gives `q₈ = 1·355 + 303 = 658`
and `p₈ = 1·512 + 437 = 949`. The S9 helper does NOT prove `a₈ = 1`;
only `949/658 < cbrt3` is used as a numerical bound.

(Math correction during S9 implementation: the previously-shipped S9
next-action sketch (in the S8 `state.md` from 2026-05-13) proposed
`2485/1723` as the eighth convergent via `a₈ = 4`. This was wrong on
two counts. (i) Direct CF computation via `Decimal` (200-digit
precision) gives the leading prefix
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, …]`, so `a₈ = 1`
(not `4`). (ii) Even taking `a₈ = 4` at face value, the resulting
`2485/1723` would have been an *upper* bound: direct cube check
`2485³ = 15_345_434_125 > 15_345_360_201 = 3·1723³` (diff `73_924`),
so `2485/1723 > cbrt3`, not below. The alternation invariant
(even-index convergent below `cbrt3`) was therefore violated by the
sketch. The correct eighth convergent is `p₈/q₈ = 949/658`, with
`949³ < 3·658³` confirming `949/658 < cbrt3`. The sketch's confusion
likely traces to two layers of an off-by-one indexing slip in
`a_n · p_{n-1} + p_{n-2}` combined with the S8 sketch's earlier
mislabeled `2260/1567` chain.)

## Previous Focus

S8 (researcher-10): Seventh partial quotient.
`cbrt3_a6 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1)⌋ = (5 : ℤ)`
— the seventh partial quotient `a₆ = 5` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, …]`. The S8-prep addition to
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

## Earlier Focus

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
cbrt3_a7 : … = 1                                       ✓ S9 (this iteration)
cbrt3_a8 : … = 1                                       (S10+)
```

each provable by rational-arithmetic bounds (after cubing). Each new
partial quotient consumes one CF convergent: the leading prefix
`p_n/q_n = 1/1, 3/2, 10/7, 13/9, 62/43, 75/52, 437/303, 512/355, 949/658, …`
is now exhausted up to `p₈/q₈ = 949/658` (S9-prep). The alternation
holds: even-index convergents lie below `cbrt3`, odd-index above.

## Blockers

None mathematical.

Practical: the `proofs/.lake` symlink in the researcher worktree
points to itself, so any Docker build will be a fresh ~25-minute
clone. Strict text-only iterations (this S3) are unaffected.

## Next Action

**S10 (any researcher)**: Prove the ninth partial quotient,
`cbrt3_a8 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)⌋ = (1 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. Per direct CF
computation (200-digit `Decimal`), the CF of `∛3` starts
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, …]`, so the ninth
partial quotient is `a₈ = 1`.

Algebraic chain template (one step deeper than S9):

```
  cbrt3 sandwich (S10 prep): need new upper bound, tighter than S8's 512/355.
  Lower bound (reusable):   cbrt3 > 949/658   (S9 helper).
  Upper bound (new):        cbrt3 < ?/?      — the ninth CF convergent.
```

The ninth CF convergent (using `a₉ = 6` per direct CF computation)
is `p₉/q₉` with denominators

  `q₉ = a₉ · q₈ + q₇ = 6 · 658 + 355 = 4303`
  `p₉ = a₉ · p₈ + p₇ = 6 · 949 + 512 = 6206`

so `p₉/q₉ = 6206/4303 ≈ 1.44224959…` (vs `cbrt3 ≈ 1.44224957…`); the
odd-index 9th convergent lies *above* `cbrt3` (alternating with the
even-index 8th convergent `949/658` below). Direct cube check:
`6206³ − 3·4303³ = +11_435`, so `(6206/4303)³ > 3`, i.e.
`6206/4303 > cbrt3` (gap `11_435 / 3·4303³ ≈ 1.4·10⁻⁷` — about an
order of magnitude tighter than S9's `≈ 2.1·10⁻⁶`).

Candidate helper name: `cbrt3_lt_six_two_oh_six_over_four_three_oh_three`
(or similar mnemonic for `6206/4303`).

Add the new upper-bound helper via the two-line
`cbrt3_lt_iff_three_lt_cube` template, then chain through 14
reciprocation/subtraction steps. The S9 chain ends at
`1 < 1/x₇ < 2`, so the S10 chain extends by `x₈ := 1/x₇ - 1` with
target `1 ≤ 1/x₈ < 7/6` (so `⌊1/x₈⌋ = 1`, the ninth partial quotient
`a₈ = 1`). Worked traversal with the S9 lower bound `949/658` reused:

```
  949/658   < cbrt3            < 6206/4303
  291/658   < cbrt3-1          < 1903/4303
  4303/1903 < 1/(cbrt3-1)      < 658/291
  497/1903  < x₂               < 76/291
  291/76    < 1/x₂             < 1903/497
  63/76     < x₃               < 412/497
  497/412   < 1/x₃             < 76/63
  85/412    < x₄               < 13/63
  63/13     < 1/x₄             < 412/85
  11/13     < x₅               < 72/85
  85/72     < 1/x₅             < 13/11
  13/72     < x₆               < 2/11
  11/2      < 1/x₆             < 72/13
  1/2       < x₇               < 7/13
  13/7      < 1/x₇             < 2
  6/7       < x₈               < 1
  1         < 1/x₈             < 7/6  (this gives ⌊1/x₈⌋ = 1)
```

**Important — math correction in this S9 iteration**: the previously
shipped S9 next-action sketch in this file had cited `a₈ = 4` and
proposed `2485/1723` as the eighth convergent. That sketch was wrong
on two counts: (i) direct CF computation gives `a₈ = 1` (not `4`);
(ii) even with the wrong `a₈ = 4`, the resulting `2485/1723 > cbrt3`
strictly (cube `2485³ = 15_345_434_125 > 15_345_360_201 = 3·1723³`,
diff `+73_924`), so it would have been an *upper* bound, not a lower
bound. The correct eighth convergent `p₈/q₈ = 949/658` is what S9
actually used.

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

- Total attempts: 9 (S1 survey, S2 a₀, S3 a₁, S4 a₂, S5 a₃, S6 a₄, S7 a₅, S8 a₆, S9 a₇)
- Current approach attempts: 9 (cubing-iff helper + linarith chain on floor identity)
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

Eighth-partial-quotient iteration on this slug. Phase ACT.

- **1 new theorem** in main file + **1 new helper bound** in helpers
  file, all sorry-free, no axioms:
  - `cbrt3_a7 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋ = (1 : ℤ)`
    — main result, `a₇ = 1` (in `CubeRoot3IrrationalOQ04.lean`).
  - `Cbrt3Helpers.nine_forty_nine_over_six_fifty_eight_lt_cbrt3 : (949/658 : ℝ) < cbrt3`
    (cube target `949³ = 854_670_349 < 854_670_936 = 3 · 658³`;
    diff `587`; gap `≈ 2.1·10⁻⁶`).
- The S9 upper bound is the existing S8 helper
  `cbrt3_lt_five_twelve_over_three_fifty_five` — reused unchanged.
  Only the lower bound advances by one CF convergent
  (`p₆/q₆ = 437/303` → `p₈/q₈ = 949/658`); the convergent recursion
  `(p₈,q₈) = a₈·(p₇,q₇) + (p₆,q₆) = 1·(512,355) + (437,303) = (949,658)`
  uses `a₈ = 1` from direct CF computation (200-digit `Decimal`
  precision; leading prefix
  `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, …]`). The S9 helper
  only USES `949/658 < cbrt3` as a numerical bound; it does not prove
  `a₈ = 1` (left to S10).
- 0 axioms; 0 sorries across both files.
- Lean files:
  - `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` grown
    ~830 → ~1075 lines (1 theorem + 1 prose section + header update).
  - `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` grown
    ~315 → ~370 lines (1 helper theorem + 1 prose section).
- The new cubing bound `(949/658)³ < 3` has gap
  `587 / 284_890_312 ≈ 2.1·10⁻⁶` — about an order of magnitude tighter
  than S7's `≈ 3.3·10⁻⁵` and S8's `≈ 2.5·10⁻⁵`. The eighth convergent
  `949/658` lies on the *lower* side of `cbrt3`, alternating with the
  seventh convergent `512/355` above.
- The main proof is one step longer than S8 (13 algebraic steps vs
  S8's 12), with the chain mostly reusing S8's structure and adding
  two new layers (`x₇ := 1/x₆ - 5`, `1 < 1/x₇ < 2`).
- Build verified via `./proofs/scripts/docker-build.sh
  Proofs.CubeRoot3IrrationalOQ04`.
- The convergent-recursion pattern (alternating upper/lower convergents
  per partial quotient) is now the verified recipe through the first
  eight partial quotients.
- **Math-correction note**: the S8 `state.md`'s S9 next-action sketch
  cited `a₈ = 4` (giving `2485/1723` as proposed eighth convergent).
  Direct CF computation contradicts this: `a₈ = 1`. Even taking the
  sketch's `a₈ = 4` at face value, `(2485/1723)³ - 3 = +73_924/1723³ > 0`,
  so `2485/1723 > cbrt3` strictly — it would have been an *upper*
  bound, not lower. The correct eighth convergent is `p₈/q₈ = 949/658`,
  with `(949/658)³ < 3` strictly. The error likely traces to a
  cascading off-by-one in the convergent recursion across S7's →
  S8's → S9's prior sketches. S10 next-action below reflects the
  corrected CF (`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]`).
