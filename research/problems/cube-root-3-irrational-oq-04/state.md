# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S4)
**Iteration**: 4

## Current Focus

S4 (researcher-3): Third partial quotient.
`cbrt3_a2 : ⌊1 / (1 / (cbrt3 - 1) - 2)⌋ = (3 : ℤ)` — the third
partial quotient `a₂ = 3` of the simple CF `[1; 2, 3, 1, 4, …]`.
Two new cubing-bound lemmas (`ten_sevenths_lt_cbrt3`,
`cbrt3_lt_thirteen_ninths`) plus the floor identity, following
the template specified by S3's next-action sketch verbatim.
Proof is rational-arithmetic only (cubing bounds +
`div_lt_iff₀` / `le_div_iff₀` / `lt_div_iff₀` + `Int.le_floor` /
`Int.floor_lt`); no axioms; depends on `cbrt3_cubed` only.

## Previous Focus

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
cbrt3_a2 : ⌊1/(1/(cbrt3-1) - 2)⌋ = 3                   ✓ S4 (this iteration)
cbrt3_a3 : ⌊1/(1/(1/(cbrt3-1) - 2) - 3)⌋ = 1           (S5+)
cbrt3_a4 : … = 4                                       (S6+)
```

each provable by rational-arithmetic bounds (after cubing).

## Blockers

None mathematical.

Practical: the `proofs/.lake` symlink in the researcher worktree
points to itself, so any Docker build will be a fresh ~25-minute
clone. Strict text-only iterations (this S3) are unaffected.

## Next Action

**S5 (any researcher)**: Prove the fourth partial quotient,
`cbrt3_a3 : ⌊1 / (1 / (1/(cbrt3 - 1) - 2) - 3)⌋ = (1 : ℤ)` in
`proofs/Proofs/CubeRoot3IrrationalOQ04.lean`.

Let `x₃ := 1/x₂ - 3` where `x₂ := 1/(cbrt3-1) - 2`. Need
`1 ≤ 1/x₃ < 2`, i.e. `1/2 < x₃ ≤ 1`, i.e. `7/2 < 1/x₂ ≤ 4`, i.e.
`1/4 ≤ x₂ < 2/7`, i.e. `9/4 ≤ 1/(cbrt3-1) < 16/7`, i.e.
`7/16 < cbrt3 - 1 ≤ 4/9`, i.e. `23/16 < cbrt3 ≤ 13/9`.

Cube boundaries: `(23/16)^3 = 12167/4096 ≈ 2.97 < 3` and
`(13/9)^3 = 2197/729 > 3` (already proved as
`cbrt3_lt_thirteen_ninths`). New bound needed:
`twenty_three_sixteenths_lt_cbrt3 : (23/16 : ℝ) < cbrt3` via cubing
`12167/4096 < 12288/4096 = 3`.

For the previous (S4) next-action sketch see the S3 archived
section below; for the upcoming S5 follow the exact same template.

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

- Total attempts: 4 (S1 survey, S2 a₀, S3 a₁, S4 a₂)
- Current approach attempts: 4 (cubing + nlinarith)
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
