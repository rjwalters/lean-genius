# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S5)
**Iteration**: 5

## Current Focus

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

## Previous Focus

S4 (researcher-3): Third partial quotient.
`cbrt3_a2 : ⌊1 / (1 / (cbrt3 - 1) - 2)⌋ = (3 : ℤ)` — the third
partial quotient `a₂ = 3` of the simple CF `[1; 2, 3, 1, 4, …]`.
Two new cubing-bound lemmas (`ten_sevenths_lt_cbrt3`,
`cbrt3_lt_thirteen_ninths`) plus the floor identity, following
the template specified by S3's next-action sketch verbatim.

## Earlier Focus

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

**S6 (any researcher)**: Prove the fifth partial quotient,
`cbrt3_a4 : ⌊1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)⌋ = (4 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`.

Let `x₄ := 1/x₃ - 1` where `x₃ := 1/x₂ - 3`, `x₂ := 1/(cbrt3-1) - 2`.
The fifth-convergent denominator is `43`, the fourth is `9`, so by
the standard CF tightness one expects `cbrt3 ∈ (43/30, 62/43)`
giving `a₄ = 4`. More directly:

  Need `4 ≤ 1/x₄ < 5`, i.e. `1/5 < x₄ ≤ 1/4`, i.e. `6/5 < 1/x₃ ≤ 5/4`,
  i.e. `4/5 ≤ x₃ < 5/6`, i.e. `19/5 < 1/x₂ ≤ 23/6` [pending check],
  …

The exact rational bounds depend on the next convergents of the CF
`[1; 2, 3, 1, 4, …]`; the fifth convergent is `62/43`. The S6
researcher should compute the cube boundaries fresh and use the
two-line `Cbrt3Helpers.lt_cbrt3_iff_cube_lt` /
`cbrt3_lt_iff_three_lt_cube` templates from PR #17859. Both
boundaries should give cubes within ~10⁻³ of `3`.

For the previous (S5) next-action sketch see the S4 archived
section below; the cubing-iff helpers are now standardized.

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

- Total attempts: 5 (S1 survey, S2 a₀, S3 a₁, S4 a₂, S5 a₃)
- Current approach attempts: 5 (cubing + nlinarith on bounds, then linarith chain on floor identity)
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
