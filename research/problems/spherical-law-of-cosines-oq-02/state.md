# Research State: spherical-law-of-cosines-oq-02

## Current State
**Phase**: ORIENT (S2a PREP round 2 — rotZ bearer pinned)
**Path**: full
**Since**: 2026-05-14 ~21:15 UTC
**Iteration**: 3 (S2a PREP round 2)

## Current Focus

S2a PREP round 2 — **rotZ construction bearer pinned to
`LinearEquiv.isometryOfInner`**. The prior S2a PREP (PR #18647) pivoted onto
`Measure.toSphere` and flagged R1 (`rotZ` construction `match` vs `Matrix.toLin`)
as Medium risk (~50–70 LOC). This round-2 audit identifies the direct bearer
chain `LinearEquiv.isometryOfInner` (`Mathlib/Analysis/InnerProductSpace/LinearMap.lean:140`)
and provides verbatim Lean code (~45 LOC) for the S2a-α implementer.

Deliverable: `sessions/2026-05-14-s2a-prep-rotZ-bearer-isometryOfInner.md`
(this PR), plus this state-sync.

**R1 status: RESOLVED.** S2a-α difficulty drops from Medium to Medium-Easy.

## Active Approach

S2a PREP round 2: bearer audit + verbatim Lean snippet. No Lean code touched.
The OBSERVE phase remains the lune-decomposition (Lhuilier 1782) plan; the
PREP rounds firm up specific implementation details before the first ACT.

## Attempt Count
- Total attempts: 3 (S1 OBSERVE, S2a PREP round 1, S2a PREP round 2)
- Current approach attempts: 1 (this round-2 audit)
- Approaches tried: 1 (lune-decomposition via `Measure.toSphere`)

## Blockers

**Mathlib v4.26.0 audit results** (cumulative across S2a PREP rounds 1 + 2):

- **Sphere measure** — *resolved*. `Measure.toSphere` at
  `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:47` provides the
  canonical surface measure on the unit sphere with the correct calibration
  (`toSphere_apply_univ = dim E · volume(ball 0 1)`, giving 4π for `Fin 3`).
- **3-D rotation around z-axis** — *resolved*. Build via §2 of round-2 PREP:
  `LinearEquiv.isometryOfInner` applied to a hand-rolled `LinearEquiv` with
  explicit `Fin 3 → ℝ` components. ~45 LOC.
- **Cauchy-additivity-with-monotonicity step (S2a-β)** — still open. Mathlib
  has no `AddMonoidHom.linearOfMonotone` at v4.26.0; needs ~30-40 LOC of
  dyadic-approximation bookkeeping.
- **`Complex.arg` vs `Real.Angle` for wedge definition (R3)** — implementer
  choice, defer to S2a-α ACT.

## Next Action

**S2a-α ACT**: copy the verbatim §2 Lean snippet from
`sessions/2026-05-14-s2a-prep-rotZ-bearer-isometryOfInner.md` into
`proofs/Proofs/SphericalLawOfCosinesOQ02.lean`. Docker-build, fix any `simp`
lemma-name drift (see round-2 PREP §7.2 fallback). Expected ~45 LOC for rotZ,
~25 LOC for wedge/lune/solidAngle definitions = **~70 LOC for S2a-α** (was
prior PREP estimate of 70 LOC, but with the §2 snippet pinned the risk class
drops from Medium to Medium-Easy).

Following S2a-α, the S2a-β/γ steps (~130 LOC) then complete the
`lune_solidAngle_eq_two_theta` certificate. S2b assembles the six-lune cover
identity. S2c proves the Girard theorem.

**Revised total S2 LOC budget**: ~335 LOC (was ~360 in prior PREP; ~−25 from
rotZ-bearer pin).

## Open PRs
- This PR (S2a PREP round 2, doc-only — ~+345 LOC across state.md and
  `sessions/2026-05-14-s2a-prep-rotZ-bearer-isometryOfInner.md`).

## Iteration History (recent)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-5 | #18351 (merged) | OBSERVE — Lhuilier lune-decomposition roadmap, 3-sub-iteration S2 plan (~250 LOC), spherical-measure gap flagged |
| S2a PREP r1 | 2026-05-13 | researcher-10 | #18647 (merged) | PREP — `Measure.toSphere` pivot, 4 Mathlib bearers audited, S2a split into α/β/γ, R1–R8 risk register |
| S2a PREP r2 | 2026-05-14 | researcher-3 | (this PR) | PREP — R1 resolved via `LinearEquiv.isometryOfInner` bearer pin + verbatim ~45-LOC rotZ snippet; 5 alternative routes rejected with cited reasons |
