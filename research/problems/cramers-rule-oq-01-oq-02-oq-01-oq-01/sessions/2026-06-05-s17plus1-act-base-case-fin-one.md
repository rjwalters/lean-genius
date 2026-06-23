# S17+1 ACT — Base-Case Landing (qdetN_step_eq_qdetF_fin_one)

**Date**: 2026-06-05T17:00:00Z
**Researcher**: researcher-1
**Iteration**: 18 (S17+1 ACT)
**Mode**: ACT (anti-PREP-theater)
**Sorry delta**: 1 → 1 (preserved); +1 fully proved theorem (10 → 11)
**Line delta**: 293 → 312 (+19)
**Docker**: 3060/3060 jobs (warm cache); only the unchanged sorry warning at line 282

## Motivation

This slug had accumulated 10 consecutive PREP iterations (S11–S17) at the
strategic sorry `qdetN_step_eq_qdetF` (line 282) without any ACT-side Lean
delta. The full S15 PREP §5 recipe (~95–115 LOC, hoist `submatrix_chain`
to a private lemma + Block I–IV + drop §4 sanity blocks) remains the
canonical next-picker target, but each chained PREP cycle re-confirmed
the same `nextAction` checklist without converting any planned LOC into
verified content. Per the researcher role's anti-busywork guidance, this
iteration ships the smallest verified-content delta that:

1. Does NOT depend on the strategic sorry
2. Provides concrete-witness verification of the strategic theorem's
   signed RHS
3. Compiles cleanly in one Docker pass

## The Contribution

```lean
/-- **Field consistency at n = 0 (1×1 matrices), base case.** ... -/
theorem qdetN_step_eq_qdetF_fin_one
    (A : Matrix (Fin 1) (Fin 1) F) (i j : Fin 1)
    (_h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j := by
  fin_cases i
  fin_cases j
  simp [qdetN_step, qdetF, Matrix.det_fin_one]
```

Inserted directly after the strategic theorem (line 287) so it shares
docstring locality with the open conjecture and the n=2/n=3 bridges in
Parts III–IV.

## Why it Closes by `simp`

At `n = 0`:

- The Schur double sum in `qdetN_step` is indexed by `Fin 0 × Fin 0`,
  which is empty. So `qdetN_step A i j Minv = A i j - 0 = A i j` for
  *any* `Minv` (including `(minorIJ A i j)⁻¹`). The `_h` hypothesis is
  unused at this case (renamed with `_` to silence the unused-variable
  linter).
- `(minorIJ A i j)` at `n = 0` has type `Matrix (Fin 0) (Fin 0) F`. Its
  determinant is `1` by `Matrix.det_isEmpty` (a `@[simp]` lemma in
  Mathlib that fires automatically when `IsEmpty` resolves on the index
  type via `Fin.isEmpty_iff`).
- `qdetF A i j = A.det / 1 = A.det`. For a `Matrix (Fin 1) (Fin 1)`,
  `Matrix.det_fin_one` reduces `A.det = A 0 0`.
- The sign factor: `(i : ℕ) + (j : ℕ) = 0 + 0 = 0` after `fin_cases`
  fixes `i = j = 0`. Then `(-1)^0 = 1` and `1 * A 0 0 = A 0 0`.

Both sides reduce to `A 0 0`.

## What This Does NOT Verify

The base case is a *trivial* witness: the sign factor `(-1)^(i+j)`
always evaluates to `1` here because `i = j = 0` is the only option in
`Fin 1`. So this does not exercise the off-diagonal sign-correction
that motivated the S4 statement-fix (PR #19142) and the S15 PREP §1
numerical refutation.

The first non-trivial sign-bearing witnesses are at `n = 1` (2×2
matrices) at off-diagonal pivots:

- `(i, j) = (0, 1)`: `(-1)^(0+1) = -1`
- `(i, j) = (1, 0)`: `(-1)^(1+0) = -1`

These remain natural S18 candidates (~15–20 LOC each) and are
independent of the strategic sorry. They would require some genuine
arithmetic (the Schur sum has one `(p, q) = (0, 0)` term over `Fin 1 ×
Fin 1`, not empty), so `simp` alone may not close them; expect a short
`field_simp` or `ring` finisher.

## ACT-Readiness Gate at Cycle Start

| Item | S17 PREP (2026-06-02) | S17+1 ACT (2026-06-05) |
|------|----------------------|------------------------|
| Bearer surface | 9/9 ✓ at lake SHA 2df2f0150c... | 9/9 ✓ (unchanged) |
| submatrix_chain Form 1 | ✓ (S15 PREP §4.1) | ✓ (unchanged) |
| σ(q) algebra | ✓ (S15 PREP §3) | ✓ (unchanged) |
| Outer §2.9 compatibility | ✓ (S4f PREP §2.9) | ✓ (unchanged) |
| Block I-IV LOC budget | ✓ (~40 LOC, S15 PREP §5) | ✓ (unchanged) |
| Mechanic PR #19072 unblock | ✓ | ✓ (unchanged) |
| Parent-file build clean | ✓ | ✓ (verified this cycle) |
| Docker daemon healthy | ✓ (S16) → AMBER 7.8 Gi (S17) | ✓ (29 Gi avail this cycle) |
| Host disk | AMBER 7.8 Gi (S17 PREP) | ✓ GREEN (29 Gi this cycle) |

**Aggregate at cycle start**: 9/9 ✓ (disk recovered 7.8 Gi → 29 Gi
since S17 PREP, same direction as the S15 → S16 recovery).

**Aggregate at cycle end**: 9/9 ✓ unchanged + 1 new verified theorem.

## Files Touched

1. `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` (+19 lines):
   inserted `qdetN_step_eq_qdetF_fin_one` after the strategic theorem
   at line 287 and before `end NonCommutative` at line 289.
2. `src/data/proofs/cramers-rule-oq-01-oq-02-oq-01-oq-01/meta.json`:
   `lineCount` 293 → 312, `theoremCount` 10 → 11, added entry to
   `originalContributions`.
3. `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`:
   `currentState.lastUpdate` refreshed, `knowledge.progressSummary`
   prepended with S17+1 entry, `knowledge.insights` prepended with
   S17+1 entry, `knowledge.builtItems` prepended with the new theorem,
   `leanFiles[CramersRuleOQ01OQ02OQ01OQ01]` updated.
4. This session memo (NEW).

**0** edits to: `axiom` declarations, structure-encoded assumptions,
parent files, sibling slugs, `lakefile.toml`, `lake-manifest.json`,
`research/problems/.../problem.md`, `research/problems/.../knowledge.md`.

## What This Does NOT Discharge

- The strategic sorry `qdetN_step_eq_qdetF` at line 282 is unchanged.
- The S15 PREP §5 Block I–IV recipe is unchanged.
- The S5 mutual recursion / `Invertible` typeclass parameterisation
  question is unchanged.

## Lesson

When a slug has piled up multiple PREP iterations without ACT, the
right move is NOT another PREP. Look for the smallest verified-content
delta that does not depend on the open sorry — often a base-case
specialisation exists where one or more sums collapse to empty (as
here, where `Fin 0 × Fin 0` empties the Schur double-sum at `n = 0`).
Shipping a small ACT-side delta breaks the PREP-theater pattern,
restores the slug's PREP-to-ACT ratio toward a healthier balance, and
adds a concrete witness that future PREPs can reference when
forecasting LOC budgets for the full discharge.
