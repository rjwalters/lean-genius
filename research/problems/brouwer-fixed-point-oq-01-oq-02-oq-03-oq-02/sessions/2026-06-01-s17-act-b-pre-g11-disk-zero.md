# S17 ACT-B-PRE — G11 companion file (`H_n_minus_1_disk_zero_substantive`)

- **Date**: 2026-06-01
- **Session**: 18 (S1–S16)
- **Phase**: ACT-B-PRE (closes Gap-2 of S15 PREP §4.1 — pre-stages the
  main-file integration of S16 ACT-B)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged)
- **Scope**: ships `proofs/Proofs/BrouwerFixedPointOQ01OQ02G11.lean`
  (single-theorem companion file, 73 LOC including docstring) plus the
  `proofs/Proofs.lean` rollup catch-up (G10 + G11) and this session memo.
  Doc-only updates to JSON `currentState.*` + `builtItems`. No edits to
  main file, no edits to G6/G7/G8/G10, no `axiom` delta, no `sorry`, no
  `meta.json` (slug has no gallery directory).

## 1. What this PR delivers

The Gap-2 closer recommended by S15 PREP §4.1, shipped as a fresh
companion file rather than as an in-line edit to the main file. Single
theorem in namespace `BrouwerOQ01OQ02`:

* **`H_n_minus_1_disk_zero_substantive`** — for `n ≥ 2`, the `(n-1)`-th
  singular homology of `TopCat.disk.{0} n` with `ℤ`-coefficients
  vanishes. The proof transports `H_n_minus_1_ball_zero_substantive`
  (main:310, on the raw subtype carrier `↥(Metric.closedBall …)`) along
  the homeomorphism `Homeomorph.ulift : ULift X ≃ₜ X`, promotes to a
  TopCat iso via `TopCat.isoOfHomeo`, pushes through the singular-
  homology functor with `Functor.mapIso`, and applies
  `Limits.IsZero.of_iso`.

This closes **Gap-2** of S15 PREP — the ULift universe mismatch between
the ball-side substantive theorem (raw subtype) and the sphere-side
substantive theorem (ULift-wrapped). With G10 (Gap-1) and G11 (Gap-2)
both on main, the remaining S16 ACT-B integration into the main file is
reduced to: 4 imports + n=1 branch decision + the S15 PREP §5 paste-
ready body.

## 2. Docker build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G11
...
✔ [3309/3309] Built Proofs.BrouwerFixedPointOQ01OQ02G11 (27s)
Build completed successfully (3309 jobs).
=== Build succeeded ===
```

**3309 jobs**, ~27s wall for the G11 step itself (cold-cache total
wall ~4 min including Mathlib cache download via `lake exe cache get`).
Matches the G10 import-closure cost: G11 adds only
`Mathlib.Topology.Category.TopCat.ULift` to the surface that G10 already
brought in via `Mathlib.Topology.Category.TopCat.Sphere`. The
`TopCat.ULift` module is small (60 LOC, see §3); the dominant cost
remains `TopCat.Sphere`'s transitive closure (`PiL2`, `EpiMono`).

## 3. Bearer audit at pinned rev `2df2f0150c…`

All Mathlib bearers used in this PR were spot-checked via the GitHub
`/repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c…`
API at S17 author time. No drift detected.

| Bearer | Module | Line | Used for |
|---|---|---|---|
| `TopCat.isoOfHomeo` | `Mathlib/Topology/Category/TopCat/Basic.lean` | 174 | Promote `≃ₜ` to TopCat `≅` (closes Gap-2 risk F3) |
| `Homeomorph.ulift` | `Mathlib/Topology/Homeomorph/Lemmas.lean` | 275 | `ULift X ≃ₜ X` (the underlying homeomorphism) |
| `Limits.IsZero.of_iso` | `Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean` | 115 | Transport `IsZero` along iso (signature: `IsZero Y → (X ≅ Y) → IsZero X`) |
| `TopCat.disk` (= `TopCat.of (ULift (Metric.closedBall …))`) | `Mathlib/Topology/Category/TopCat/Sphere.lean` | 28 | The target TopCat object |
| `TopCat.uliftFunctor` / `uliftFunctorObjHomeo` | `Mathlib/Topology/Category/TopCat/ULift.lean` | 30, 35 | Imported (not used directly — `Homeomorph.ulift` is enough) |

**Risk F3 (MEDIUM) of S15 PREP §6 is DISCHARGED**: `TopCat.isoOfHomeo`
is present at the pinned rev in the canonical location
(`Mathlib/Topology/Category/TopCat/Basic.lean:174`). No fallback to
`Iso.ofHom` over `TopCat.ofHom Homeomorph.toContinuousMap` is needed.

## 4. Closure of Gap-2 vs. S15 PREP §4.1

S15 PREP §4.1 sketched:
```lean
have hHomeo : TopCat.of ↥(Metric.closedBall …) ≅ TopCat.disk.{0} n :=
  TopCat.isoOfHomeo Homeomorph.ulift.symm
exact hball.of_iso (((singularHomologyFunctor … (n-1)).obj
  (AddCommGrpCat.of ℤ)).mapIso hHomeo)
```

The realized G11 reverses the homeomorphism direction. Reason:
`Limits.IsZero.of_iso` has the signature `IsZero Y → (X ≅ Y) → IsZero X`
(target gets `IsZero`, iso runs target → source). The realized proof
uses `Homeomorph.ulift : ULift X ≃ₜ X` (not `.symm`), yielding the iso
`TopCat.disk.{0} n ≅ TopCat.of ↥(closedBall)` (disk on the left, ball
on the right), so that `hball.of_iso (F.mapIso (TopCat.isoOfHomeo
Homeomorph.ulift))` concludes `IsZero (F.obj (TopCat.disk.{0} n))` from
`hball : IsZero (F.obj (TopCat.of ↥(closedBall)))`.

The PREP §4.1 sketch had the iso direction backwards (ball ≅ disk) but
combined with the `.of_iso` argument order would still have typechecked
via `e.symm.symm = e`. The realized version is shorter — no `.symm`
call.

## 5. One-shot build (no iteration)

Unlike G10 (3 attempts to close `section_identity`), G11 built green on
the first attempt. Reasons:

- The proof body is a single `exact` chain (no `ext`/`apply` ULift+Subtype
  unwrap). The `Homeomorph.ulift` instantiation handles the ULift wrap
  in one step.
- `IsZero.of_iso` is a stable Mathlib API; no unused-simp-argument
  failure mode.
- The bearer audit pre-discharged the F3 risk (TopCat.isoOfHomeo
  presence at the pinned rev), so no fallback path was needed.

## 6. `proofs/Proofs.lean` rollup catch-up

The auto-generated rollup `proofs/Proofs.lean` was missing
`import Proofs.BrouwerFixedPointOQ01OQ02G10` (orphan since PR #21922 /
S16 ACT-A). This PR's rollup regeneration adds both G10 (S16 catch-up,
2-line drift fix) and G11 (this PR, 1-line addition). Net diff vs
`origin/main`:

```diff
@@ -318,6 +318,8 @@ import Proofs.BoundedPrimeGapsTPC
 import Proofs.BrouwerFixedPoint
 import Proofs.BrouwerFixedPointOQ01
 import Proofs.BrouwerFixedPointOQ01OQ02
+import Proofs.BrouwerFixedPointOQ01OQ02G10
+import Proofs.BrouwerFixedPointOQ01OQ02G11
 import Proofs.BrouwerFixedPointOQ01OQ02G6
 import Proofs.BrouwerFixedPointOQ01OQ02G7
 import Proofs.BrouwerFixedPointOQ01OQ02G8
```

Without this catch-up, both G10 and G11 would remain orphans that
`lake build` (default target `Proofs`) does not exercise — they would
only build under an explicit `lake build Proofs.BrouwerFixedPoint…G11`
target, as this PR's Docker-verify did. The rollup catch-up ensures the
full `Proofs` target also builds them.

## 7. On-disk reality (this PR, 2026-06-01)

| File | LOC | Theorems | Definitions | Axioms | Sorries |
|------|-----|----------|-------------|--------|---------|
| `BrouwerFixedPointOQ01OQ02.lean` | 462 | 14 | … | 4 | 0 |
| `BrouwerFixedPointOQ01OQ02G6.lean` | 88 | 4 + 1 local | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G7.lean` | 94 | 2 | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G8.lean` | 134 | 2 | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G10.lean` | 78 | 1 | 1 | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G11.lean` | **73** | **1** | … | **0** | **0** |
| **Total** | **929** | **25** | **1** | **4** | **0** |

Net delta this PR: +73 LOC, +1 theorem, +0 definitions, +0 axioms,
+0 sorries (plus +2 lines in `Proofs.lean`).

## 8. What this unblocks for S18 ACT-B (main-file integration)

With G10 (Gap-1) + G11 (Gap-2) both on main, the S18 ACT-B integration
is the substantive replacement of the mock axiom
`H_n_minus_1_sphere_nonzero` (main:261) with:

1. Imports: `Proofs.BrouwerFixedPointOQ01OQ02G6/G7/G8/G10/G11`.
2. Body (per S15 PREP §5 paste-ready):
   - For `n ≥ 2`: G8 functoriality on `(diskBoundaryInclusion,
     r.toTopCatHom)` + G9 retract-of-zero + G11 disk-zero ⇒ IsZero on
     `H_{n-1}(∂𝔻 n)`; contradict
     `H_n_minus_1_sphere_nonzero_substantive` (main:375); then G7+G6
     extract the `∃ ψ, ψ ∘ φ = id` shape.
   - For `n = 1`: `Retraction 1` uninhabited via IVT (knowledge.md
     §G5 / main:303); ship as thin local axiom
     `Retraction_one_uninhabited` (axiom net 4→4) or a 5-line IVT proof
     (axiom net 4→3).

Expected S18 build size: ~3300–3400 jobs (main-file rebuild, same
import closure as G10/G11). Wall clock per cache state: warm ~30s
incremental, cold ~4 min full Mathlib download.

## 9. Anti-targets (S17 ACT-B-PRE)

- No edits to `BrouwerFixedPointOQ01OQ02.lean` (mock-axiom removal
  deferred to S18 ACT-B per the recommended split).
- No edits to G6/G7/G8/G10 (already on main, build verified).
- No `meta.json` updates (slug has no gallery directory; verified
  `src/data/proofs/brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02/`
  does not exist).
- No upstream Mathlib contribution (B1 / B2 still on the queue).
- No `state.md` edits in this PR (deferred to S18 STATE-SYNC; the JSON
  catch-up here is sufficient for the next session to pick up).

## 10. Honesty notes

- The build matched the G10 cost (3309 jobs) rather than the
  PREP §7 estimate (~400–500 jobs in isolation). The G10 session memo
  (S16 ACT-A) already recorded the cost surprise; this PR adds no new
  surprise — the `TopCat.Sphere` import closure dominates whenever
  G10 / G11 is built, independent of the file size.
- The S15 PREP §4.1 iso direction was technically backwards but
  recoverable via `.symm`; the realized G11 uses the natural direction
  and saves one `.symm` call. Cosmetic.
- The mock axiom `H_n_minus_1_sphere_nonzero` (main:261) is still
  live in this PR. Net axiom delta: 0. The retirement is the S18
  deliverable.
- The recommended n=1 axiom-count expectation remains 4→4 (replace
  mock composite with thin IVT axiom), not the JSON's predicted
  4→3 — see S15 PREP §10 third bullet.
- The `proofs/Proofs.lean` rollup catch-up is a minor housekeeping fix
  for an orphan that S16 ACT-A introduced; it is not the primary
  deliverable of this PR. The primary deliverable is G11 + the
  Docker-verified close of Gap-2.
