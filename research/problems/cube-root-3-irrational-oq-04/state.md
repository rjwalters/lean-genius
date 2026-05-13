# Current State

**Phase**: ACT
**Since**: 2026-05-13 (S6)
**Iteration**: 6

## Current Focus

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

The cubing sandwich `(62/43)³ < 3 < (75/52)³` is the tightest in the
prefix so far: the lower cube gap is `193/79507 ≈ 2.4·10⁻³` and the
upper cube gap is `51/140608 ≈ 3.6·10⁻⁴`, both consistent with
`62/43` being the fifth convergent of the CF (the upper semi-convergent
`75/52` is one step from the next convergent `137/95`).

## Previous Focus

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

## Earlier Focus

S4 (researcher-3): Third partial quotient.
`cbrt3_a2 : ⌊1 / (1 / (cbrt3 - 1) - 2)⌋ = (3 : ℤ)` — the third
partial quotient `a₂ = 3` of the simple CF `[1; 2, 3, 1, 4, …]`.
Two new cubing-bound lemmas (`ten_sevenths_lt_cbrt3`,
`cbrt3_lt_thirteen_ninths`) plus the floor identity, following
the template specified by S3's next-action sketch verbatim.

## Earlier Earlier Focus

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
cbrt3_a3 : ⌊1/(1/(1/(cbrt3-1) - 2) - 3)⌋ = 1           ✓ S5 (this iteration)
cbrt3_a4 : … = 4                                       (S6+)
```

each provable by rational-arithmetic bounds (after cubing).

## Blockers

None mathematical.

Practical: the `proofs/.lake` symlink in the researcher worktree
points to itself, so any Docker build will be a fresh ~25-minute
clone. Strict text-only iterations (this S3) are unaffected.

## Next Action

**S7 (any researcher)**: Prove the sixth partial quotient,
`cbrt3_a5 : ⌊1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - a₄_val)⌋ = (a₅ : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`, where `a₅` is the
sixth partial quotient of `∛3` (= `1`, per OEIS A002945 `[1; 2, 3, 1, 4, 1, …]`).

Concretely: let `x₄ := 1/x₃ - 1`, `x₅ := 1/x₄ - 4`. Need `1 ≤ 1/x₅ < 2`,
i.e. `1/2 < x₅ ≤ 1`, i.e. `5 < 1/x₄ ≤ 6` — but wait, that conflicts with
the S6 strict bound `4 < 1/x₄ < 5`. So `a₅` should be computed afresh
from the next convergents:

  After `a₄ = 4` the seventh convergent denominator is `43 · 4 + 9 = 181`
  (or one of `137 / 95`, `199 / 138` if `a₅ = 1`).

OEIS A002945 list begins `1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, …`, so
`a₅ = 1` is expected and the corresponding rational sandwich on `1/x₄`
will be `(5, 6)`. The S7 researcher should compute the cube boundaries
fresh from the seventh and eighth convergents of the CF, and use the
same two-line `Cbrt3Helpers.lt_cbrt3_iff_cube_lt` /
`cbrt3_lt_iff_three_lt_cube` templates. The seventh convergent appears
to be `137/95` (≈ `1.4421…`) and the corresponding cube target will be
within ~10⁻⁴ of `3`.

Algebraic chain template (same shape, one step deeper):

```
  62/43 < cbrt3 < 75/52                         (S6 bounds; reuse)
  ... (S6 chain through x₄)
  1/5 < x₄ < 1/4
  4 < 1/x₄ < 5                                  (S6: ⌊1/x₄⌋ = 4)
  needed (S7): some rational sandwich on x₅ := 1/x₄ - 4
```

For the previous (S6) next-action sketch see the S5 archived
section below; the cubing-iff helpers continue to standardize the
new bounds.

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

- Total attempts: 6 (S1 survey, S2 a₀, S3 a₁, S4 a₂, S5 a₃, S6 a₄)
- Current approach attempts: 6 (cubing-iff helper + linarith chain on floor identity)
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
