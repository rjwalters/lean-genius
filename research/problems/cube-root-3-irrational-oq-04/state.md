# Current State

**Phase**: ACT
**Since**: 2026-05-11 (S2)
**Iteration**: 2

## Current Focus

S2 (researcher-10): First Lean iteration. Established
`cbrt3_floor_eq_one : ⌊cbrt3⌋ = (1 : ℤ)` — the leading partial
quotient `a₀ = 1` of the simple continued fraction `[1; 2, 3, 1, 4, …]`.
Proof is real-arithmetic only (cubing bounds + `Int.le_floor` /
`Int.floor_lt`); no axioms; depends on `cbrt3_cubed` only.

## Active Approach

**Finite-prefix verification, no full-sequence claim.**

The CF of `∛3` is non-periodic (Lagrange), so the deliverable is a
chain of lemmas

```
cbrt3_a0 : ⌊cbrt3⌋ = 1
cbrt3_a1 : ⌊1/(cbrt3 - 1)⌋ = 2
cbrt3_a2 : … = 3
cbrt3_a3 : … = 1
cbrt3_a4 : … = 4
```

each provable by rational-arithmetic bounds (after cubing).

## Blockers

None mathematical.

Practical: the `proofs/.lake` symlink in the researcher worktree
points to itself, so any Docker build will be a fresh ~25-minute
clone. Strict text-only iterations (this S1) are unaffected.

## Next Action

**S3 (any researcher)**: Prove the second partial quotient,
`cbrt3_a1 : ⌊1 / (cbrt3 - 1)⌋ = (2 : ℤ)` in
`proofs/Proofs/CubeRoot3IrrationalOQ04.lean`.

Equivalent to `2 ≤ 1/(cbrt3 - 1) < 3`, i.e.
`1/3 < cbrt3 - 1 ≤ 1/2`, i.e. `4/3 < cbrt3 ≤ 3/2`. After cubing
and substituting `cbrt3 ^ 3 = 3`: `64/27 < 3 ≤ 27/8`. Both
inequalities hold strictly (`64/27 ≈ 2.37`, `27/8 = 3.375`), so the
`≤ 3/2` is in fact strict, giving `2 < 1/(cbrt3 - 1) < 3` and the
floor identity.

Provability sketch (analogous to S2 — `nlinarith` after cubing):

```lean
theorem four_thirds_lt_cbrt3 : (4/3 : ℝ) < cbrt3 := by
  by_contra h; push_neg at h
  have h2 : cbrt3 ^ 3 ≤ 64/27 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]; nlinarith [h, cbrt3_nonneg]
  rw [cbrt3_cubed] at h2; linarith

theorem cbrt3_lt_three_halves : cbrt3 < (3/2 : ℝ) := by
  by_contra h; push_neg at h
  have h2 : (27/8 : ℝ) ≤ cbrt3 ^ 3 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]; nlinarith [h, cbrt3_nonneg]
  rw [cbrt3_cubed] at h2; linarith
```

Then combine with `Int.floor_eq_iff` and `div_lt_iff_lt_mul` /
`lt_div_iff_mul_lt` style algebra (or shortcut via
`Int.floor_div_one_sub` if such a lemma exists in Mathlib).

## Attempt Counts

- Total attempts: 2 (S1 survey, S2 first-partial-quotient lemma)
- Current approach attempts: 2 (cubing + nlinarith)
- Approaches tried: 1

## Open files

- `problem.md` — Mathlib infrastructure map, theoretical obstacle
  (Lagrange's theorem), suggested prefix decomposition.
- `knowledge.md` — S1 session note: prefix derivation `[1; 2, 3,
  1, 4, …]`, first five convergents `1/1, 3/2, 10/7, 13/9, 62/43`,
  Mathlib API name list, OEIS pointer.

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
