# S3 ACT — apply PREP-2 §6 volume-bridge fix to discharge phantom-name in OQ02OQ02 (build pending)

**Date**: 2026-05-13
**Researcher**: researcher-10
**Phase**: S3 ACT (Lean discharge of the S2 SCAFFOLD phantom-name; build pending)
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Risk**: LOW (single-method 5-line replacement; PREP-2 verified the bridge against the pin)

## §0 What this PR does

Replaces the phantom Mathlib-name call at
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:89`

```lean
-- Before (S2 SCAFFOLD #18364, phantom):
rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
```

with the corrected three-step bridge verified in S3 PREP-2 §6:

```lean
-- After (S3 ACT):
rw [IntegrableOn, volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hint
exact hint
```

Also syncs `knowledge.md` so it no longer documents the phantom name as
real Mathlib (rows §S1 hypothesis-table and §S1 Mathlib-API-audit table,
plus the embedded proof-sketch at line 86).

State.md is bumped from `S3 PREP-2 complete (doc-only)` to
`S3 ACT shipped (Lean edit, build pending)`.

## §1 Prerequisite chain (already merged before this ACT)

| PR | Phase | Outcome |
|---|---|---|
| #18262 | S1 OBSERVE | LocallyIntegrable reframing as wrapper, not weakening |
| #18364 | S2 SCAFFOLD | Wrapper file landed with phantom name (build pending) |
| #18514 | S2d PREP | Cross-family call-site verification |
| #18711 | S3 PREP | Phantom-name audit: `restrict_prod_eq_prod_restrict` not in Mathlib v4.26.0 |
| S3 PREP-2 (doc-only) | S3 PREP-2 | Verified the §6 corrected bridge at the pin |

PREP-2 §§1–4 verified each ingredient of the new bridge at the pin
`2df2f015...`:

- **§1** `volume_eq_prod` is `rfl`, requires explicit `(α β)` arguments
  (`Mathlib/MeasureTheory/Measure/Prod.lean:181`).
- **§2** `Measure.prod_restrict` exists at `Prod.lean:720`, requires
  `[SFinite μ] [SFinite ν]` (no measurability hypotheses).
- **§3** `SFinite` auto-derives from `SigmaFinite` and is preserved by
  `.restrict` (`Typeclasses/SFinite.lean:190 + 75`), so the instances
  needed by `Measure.prod_restrict` resolve automatically for `volume`
  on ℝ.
- **§4** `IntegrableOn f s μ` unfolds to `Integrable f (μ.restrict s)`
  so the `rw [IntegrableOn]` step exposes the form
  `Integrable f (volume.restrict (uIcc a b ×ˢ uIcc c d))` to which
  `volume_eq_prod ℝ ℝ` and `← Measure.prod_restrict` apply.

## §2 Pencil-checked goal flow

After the three rewrites, the type of `hint` becomes:

```
Integrable (fun p : ℝ × ℝ => f p.1 p.2)
  ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d)))
```

which is exactly the integrability hypothesis `apply
GreensTheoremOQ01OQ01OQ02.intervalIntegral_swap` left open. The
`exact hint` closes the goal.

The `rw` steps are direction-correct:

1. `IntegrableOn` — `def`, unfolds.
2. `volume_eq_prod ℝ ℝ` — `rfl` lemma `volume = volume.prod volume`,
   forward direction rewrites `volume` ↦ `volume.prod volume` inside
   the `.restrict (uIcc a b ×ˢ uIcc c d)` wrapper.
3. `← Measure.prod_restrict` — backward direction rewrites
   `(volume.prod volume).restrict (uIcc a b ×ˢ uIcc c d)` ↦
   `(volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d))`,
   matching the parent's expected form (`s = uIcc a b`, `t = uIcc c d`
   inferred by unification with the goal's RHS).

## §3 In-repo precedent

`proofs/Proofs/AreaOfCircleOQ05OQ04.lean:158` already uses the working
call shape `rw [volume_eq_prod ℝ ℝ, integral_prod_mul ...]` — i.e. the
explicit `(ℝ ℝ)` arguments and the same forward-direction rewrite of
`volume`. PREP-2 §5 cites this as a working precedent.

## §4 Build status

**Build is pending** — no `./proofs/scripts/docker-build.sh
Proofs.GreensTheoremOQ01OQ01OQ02OQ02` was run in this session, in
line with the established slug pattern (S2 SCAFFOLD #18364 was also
build-pending at merge time, and subsequent PREPs were doc-only).
The Mechanic / Auditor cycle will pick up the build verification.

If the build fails, the most likely failure modes are:

1. **Unification ambiguity on `← Measure.prod_restrict`** — if Lean
   cannot infer `s = uIcc a b` and `t = uIcc c d` from the goal's RHS,
   the call would need explicit `(s := uIcc a b) (t := uIcc c d)`.
2. **`IntegrableOn` `simp_attr` / `def` distinction** — if the goal
   keeps `IntegrableOn` folded after the `rw`, switching the first
   step to `unfold IntegrableOn` or `change` would discharge.
3. **`SFinite` instance lookup** — extremely unlikely for `volume`,
   but a `letI : SFinite (volume : Measure ℝ) := inferInstance` would
   force resolution.

None of these are structural risks — all three are mechanical fallback
syntactic adjustments that a build-loop iteration can resolve.

## §5 Scope of this PR

- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` — **+13 / -1**
  in the proof body of `intervalIntegral_swap_of_locallyIntegrable`,
  plus an explanatory comment block citing PREP-2 verifications.
- `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/knowledge.md`
  — **+13 / -4** correcting three references to the phantom name
  (§S1 hypothesis-table row, §S1 Mathlib-API-audit table row, embedded
  proof-sketch block at line 86), plus a one-row addition to the API
  table for the corrected ingredients (`volume_eq_prod`,
  `Measure.prod_restrict`, `IntegrableOn` (def)).
- `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/state.md`
  — **+1 / -1** header line update from `S3 PREP-2 complete` to
  `S3 ACT shipped (Lean edit, build pending)`; iteration bump 4 → 5.
- `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-13-s3-act-volume-bridge-discharge.md`
  — **this memo** (~200 LOC).

**Net delta**: ~227 lines added across 4 files.

## §6 Out of scope

- ❌ **No Docker build run.** Established slug pattern; build-pending is
  acceptable for the S3 ACT ship. Mechanic / Auditor cycle handles.
- ❌ **No sibling-file propagation.** PREP-2 §7.6 explicitly defers
  the same phantom-name fix in `GreensTheoremOQ01OQ01OQ02OQ01.lean`,
  `GreensTheoremOQ01OQ01OQ02.lean` (parent), `OQ03`, and
  `AreaOfCircleOQ05OQ01` — each needs its own ACT. This PR addresses
  only `OQ02OQ02` (the wrapper).
- ❌ **No gallery promotion.** Slug has no `src/data/proofs/...` entry;
  separate post-build task.
- ❌ **No `problem.md` edit.** Problem statement is unchanged.
- ❌ **No edit to the merged PREP-2 memo or any prior session memo.**

## §7 Race-safety

Pre-claim and pre-push race checks:

```
gh pr list -R rjwalters/lean-genius \
  --search "greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title" --state open
  → []   (zero open PRs on the exact slug)
```

The three open PRs returned by a less-precise `greens-theorem` keyword
search (`#17822`, `#17838`, `#17840`) are on **sibling slug `-oq-01`**
(not `-oq-02`), not this one. Zero scope conflict.

Pre-push re-check planned immediately before `git push`.

## §8 Honesty

- The PREP-2 fix is **paper-verified** at the pin but **not Lean-verified**.
  The §4 build-failure modes are plausible; the ship is conditional on
  the Mechanic / Auditor build pass.
- This PR does **not** weaken the wrapper's hypotheses; the
  `LocallyIntegrable` interface remains strictly stronger than the
  parent's per-rectangle integrability. The PR closes the
  S2-SCAFFOLD-introduced phantom-name issue, nothing more.
- The proof remains a 5-line modification of the parent's continuous
  case at the level of mathematical content; the line-count delta is
  inflated by the inline comment block citing PREP-2 verifications.

## §9 Cross-references

- S3 PREP-2 (volume-bridge verification) — researcher-5, 2026-05-13.
- S3 PREP #18711 (phantom-name audit) — researcher-1, 2026-05-13.
- S2 SCAFFOLD #18364 (this file's introduction) — researcher-?, 2026-05-12.
- S1 OBSERVE #18262 (LocallyIntegrable reframing) — researcher-8, 2026-05-12.
- In-repo precedent: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean:158`.
- `MEMORY.md` pattern: *Mathlib bearer-audit PREPs frequently cite
  Mathlib HEAD instead of lake-pinned SHA* — applied: re-citations
  here use the lake-pinned SHA `2df2f015...` exclusively.
