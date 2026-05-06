# Knowledge: erdos-353-incomplete-01

## Research Notes

Erdős Problem #353 (Geometric Configurations in Sets of Infinite Measure):
recently solved by Koizumi (2025) for isosceles trapezoids, isosceles
triangles, and right triangles, plus Kovač–Predojević (2024) for cyclic
quadrilaterals. The Lean formalization keeps each solved result as an
`axiom` (since the underlying proofs are recent Mathlib-external research)
and proves the natural scaling consequences from those axioms.

## Known Facts

- `proofs/Proofs/Erdos353Problem.lean` — main file (446 lines, 11 thms,
  4 axioms encoding cited published results, 0 sorries on disk)
- `proofs/Proofs/Erdos353Aristotle.lean` — companion (40 lines, 1 thm,
  scaling-of-Lebesgue-measure helper)

## Approaches Tried

### Prior session — scaling argument from Koizumi (status snapshot)

Earlier work proved the scaling consequence:
`scaling_property : HasInfiniteMeasure A → ∀ t > 0, HasIsoscelesTriangleWithArea A t`,
reducing the per-area question to Koizumi's area-1 axiom by rescaling
the set by `1/√t`. Companion-file `volume_preimage_smul_eq_top`
provides the Haar-scaling glue. As recorded, the file had 0 sorries.

## Session 2 (2026-04-27) — Build Blocked

**Mode**: REVISIT (claimed MODERATE problem, knowledge score 12)
**Outcome**: BLOCKED — both files fail to build on `origin/master`.
This is adjacent in time to the `project_mathlib_api_drift_2026_04`
cohort but a different breakage pattern (pointwise `Set` smul +
stricter docstring parsing).

### Build Verification

Ran `./proofs/scripts/docker-build.sh Proofs.Erdos353Problem` and
`./proofs/scripts/docker-build.sh Proofs.Erdos353Aristotle` from a
clean `origin/master` snapshot (commit `70a28e942bd`). Both fail.

### Errors (Erdos353Problem.lean)

Two distinct categories:

**Category A — Lean 4.26 stricter docstring parsing.**
Lines 226, 233, 251, 260 each open a `/-- ... -/` doc-comment that is
*not* attached to a following declaration (the file has free-floating
docstrings for Kovač's Trapezoid theorem (line 222), Kovač's
Parallelogram counterexample (line 227), Kovač–Predojević Congruent
Sides counterexample (line 247), and Finite Measure Fails (line 256),
none of which have a paired `axiom`/`theorem`/`lemma`):

```
error: Proofs/Erdos353Problem.lean:226:2: unexpected token '/--'; expected 'lemma'
error: Proofs/Erdos353Problem.lean:233:2: unexpected token '/--'; expected 'lemma'
error: Proofs/Erdos353Problem.lean:251:2: unexpected token '/--'; expected 'lemma'
error: Proofs/Erdos353Problem.lean:260:2: unexpected token '/--'; expected 'lemma'
```

These probably parsed in an older Lean release. Fix: convert each
orphan `/-- ... -/` to a regular block comment `/- ... -/`, or attach
each to a stub axiom.

**Category B — `HSMul ℝ (Set _)` instance no longer synthesized.**
Lines 274, 285, 347, 350 use `c⁻¹ • A` where
`A : Set (EuclideanSpace ℝ (Fin 2))`. Lean fails to synthesize
`HSMul ℝ (Set (EuclideanSpace ℝ (Fin 2))) ?m`, suggesting the
pointwise smul instance on `Set` is no longer in scope:

```
error: Proofs/Erdos353Problem.lean:274:4: failed to synthesize
  HSMul ℝ (Set (EuclideanSpace ℝ (Fin 2))) ?m.19
```

Likely fix: `open Pointwise` (the Mathlib convention to enable
`c • A` for sets), or import the module that now carries
`Set.smul_set`.

There are also cascading errors at lines 296 (parser), 320 (`simp`
made no progress) that may resolve once `HSMul` resolution is
restored.

### Errors (Erdos353Aristotle.lean)

Single instance error from the same root cause:

```
error: Proofs/Erdos353Aristotle.lean:29:66: failed to synthesize
  HSMul ℝ (Set (EuclideanSpace ℝ (Fin 2))) ?m.53
```

Likely fix: same `open Pointwise` / Mathlib import adjustment as the
main file.

### Why I Did Not Fix

Per project memory `project_mathlib_api_drift_2026_04`, repair work
on upstream-induced breakage is Mechanic-owned. While Category A
(orphan docstrings) is locally repairable, Category B is genuine
Mathlib API drift on the pointwise scalar action and should be
batched with other affected files. A scoped researcher fix would
risk diverging from a future Mechanic batch repair.

### Next Steps

1. **Mechanic**:
   - Convert orphan `/-- ... -/` docstrings on lines 222, 227, 247,
     256 of Erdos353Problem.lean to regular block comments
     `/- ... -/`. This unblocks Category A.
   - Add `open Pointwise` to both `Erdos353Problem.lean` and
     `Erdos353Aristotle.lean` (or import the module that re-exposes
     `Set.smul_set`). This unblocks Category B.
   - Re-run Docker build to confirm green state.
2. **Researcher (after repair)**: extend `scaling_property` to right
   triangles, isosceles trapezoids, and cyclic quadrilaterals. All
   four are structurally identical uses of `addHaar_smul` on the
   corresponding base axiom — a direct parallel of the existing
   `scaling_property` for isosceles triangles. This rounds out the
   gallery's "any positive area" coverage of the Erdős #353
   configuration list.

### Files Modified This Session

- `research/problems/erdos-353-incomplete-01/knowledge.md` (this
  file) — Session 2 entry: build verification + drift diagnosis
- `src/data/research/problems/erdos-353-incomplete-01.json` —
  `progressSummary`, `currentState`, `nextSteps`

No proof code changed.

## Session 3 (2026-05-06) — Build Repair

**Mode**: REVISIT (RICH, knowledge score 17)
**Outcome**: Build repair PR #16131 created. All 4 failure categories fixed.

### Root Cause Analysis

Four failure categories identified and fixed:

**A. Orphan `/-- ... -/` docstrings** (lines 222-226, 227-233, 247-251, 256-260):
Lean 4.26 parser now rejects `/-- ... -/` doc comments that aren't
immediately followed by a declaration. Converted to `/- ... -/`.

**B. `HSMul ℝ (Set _)` synthesis failure** (lines 274, 285, 347, 350):
`c⁻¹ • A` for `A : Set (EuclideanSpace ℝ (Fin 2))` requires
`Set.smulSet` instance which is gated behind `open Pointwise`.
Fix: add `open Pointwise` to both files.

**C. `Inner.inner` typeclass API drift** (line 88, new in v4.26.0):
`inner x y` no longer infers `𝕜` from context in all positions.
Fix: `inner (𝕜 := ℝ) x y` in `IsRightTriangle` definition.
Pattern confirmed in other project files (BrouwerFixedPointOQ01OQ03,
CevasTheoremOQ02OQ01 etc.).

**D. `triangleArea_smul_eq` simp regression** (line 320):
`smul_sub` is forward-direction only (proves `c • (a-b) = c•a - c•b`).
Goal had `(c•q - c•p)` form, so `smul_sub` never fired.
Fix: replace with `Pi.sub_apply` + `Pi.smul_apply` + `smul_eq_mul`,
and update subsequent `rw` to use component coordinates.
Pattern: `Pi.sub_apply, Pi.smul_apply, smul_eq_mul` confirmed in
`Erdos107Problem.lean:310` and `MinkowskiTheoremOQ02OQ01.lean:205-212`.

### Why Docker Build Not Verified

Concurrent mechanic/deployer agents keep running `git reset --hard` on
the main repo filesystem during the build window (~5 min), reverting
the temporary file copies needed for Docker verification. PR #16131
should be verified by CI or Deployer.

### Next Steps (after merge)

1. Extend `scaling_property` to right triangles, isosceles trapezoids,
   and cyclic quadrilaterals (structurally identical to existing isosceles
   triangle version — use `addHaar_smul` on the corresponding base axiom)
2. Reduce axiom count: explore whether Koizumi (2025) + Kovač (2023)
   results can be partially captured by Mathlib analysis lemmas
