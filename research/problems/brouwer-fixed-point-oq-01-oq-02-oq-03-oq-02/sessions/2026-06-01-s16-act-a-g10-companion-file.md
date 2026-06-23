# S16 ACT-A — G10 companion file (`Retraction.toTopCatHom` + `section_identity`)

- **Date**: 2026-06-01
- **Session**: 17 (S1–S15)
- **Phase**: ACT-A (first of the two PRs recommended by S15 PREP §8)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged)
- **Scope**: ships `proofs/Proofs/BrouwerFixedPointOQ01OQ02G10.lean` (1 def + 1 theorem) and the session memo. Doc-only updates to JSON `currentState.*` + `builtItems`. No edits to main file, no edits to G6/G7/G8, no `axiom` delta, no `sorry`, no `meta.json` (slug has no gallery directory).

## 1. What this PR delivers

The first of the two-PR split recommended by S15 PREP §8: a **new
companion file** `proofs/Proofs/BrouwerFixedPointOQ01OQ02G10.lean`
(78 LOC including docstring) installing two declarations in namespace
`BrouwerOQ01OQ02`:

* **`Retraction.toTopCatHom`** (definition, noncomputable) — the
  TopCat morphism `𝔻 n ⟶ ∂𝔻 n` built from the underlying retraction's
  continuous function. ULift wrap/unwrap, subtype restriction via
  `Continuous.codRestrict`, continuity transported through the chain
  `ULift.up ∘ codRestrict r.toFun (UnitSphere n) _ ∘ Subtype.val ∘ ULift.down`.

* **`Retraction.section_identity`** (theorem) — the section equation
  `diskBoundaryInclusion n ≫ r.toTopCatHom = 𝟙 (∂𝔻 n)` in `TopCat`.
  Proof: after `ext ⟨⟨p, hp⟩⟩`, apply `ULift.ext` + `Subtype.ext` to
  reduce to `r.toFun p = p`, which is exactly `r.fixes_sphere p hsphere`.

Closes **Gap-1** of S15 PREP. The pre-staged paste skeleton (§3.1) is
realized with two adjustments to match Mathlib v4.26.0 names actually
in the pin:

| PREP §3.1 | Realized | Reason |
|---|---|---|
| `continuous_uLift_up` | `continuous_uliftUp` | Camel-case spelling in v4.26.0 |
| `continuous_uLift_down` | `continuous_uliftDown` | Same |
| Inner subtype shape `r.maps_to_sphere p this` rewrite via `simpa [UnitSphere]` | Same (works) | Matched |

The `section_identity` proof uses the cleaner `ext + ULift.ext + Subtype.ext` chain rather than the PREP §3.1 `funext + Retraction.toTopCatHom` `simp` chain (the latter left `r.toFun p = p` as an "unused simp argument" rewrite — the `congr` step needed an explicit `ULift.ext` / `Subtype.ext` lift before `r.fixes_sphere` would close).

## 2. Docker build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G10
...
✔ [3309/3309] Built Proofs.BrouwerFixedPointOQ01OQ02G10 (64s)
Build completed successfully (3309 jobs).
=== Build succeeded ===
```

**3309 jobs**, ~64s wall on warm cache (post-Mathlib cache hit, 56 Gi
free at S15 PREP time). This is at the high end of the S15 PREP §7
estimate (~400–500 jobs for the companion file alone) — the gap is
because the companion file pulls in
`Mathlib.Topology.Category.TopCat.Sphere` (which transitively pulls in
the `module`-system `EpiMono` + `Analysis.InnerProductSpace.PiL2`),
materially increasing the import closure beyond what S15 PREP
estimated from G6/G7/G8.

**Build-cost honest update**: the §7 estimate was based on companion-
file deltas from G6 (~600 jobs) + G7 (~700 jobs) + G8 (~600 jobs).
Those companions don't import `TopCat.Sphere`. G10 does, which is why
the job count jumped to 3309 — Sphere's import closure is the bulk.

## 3. Three iterations to reach green

| Attempt | Tactic | Result |
|---|---|---|
| 1 | PREP §3.1 verbatim with `continuous_uLift_up` / `continuous_uLift_down` (S15 PREP names) | **Failed at 3309/3309**: errors at `section_identity` `show ULift.up ⟨_, _⟩ = ULift.up ⟨_, _⟩` — `⟨...⟩` notation needs explicit type |
| 2 | Replaced `show` with `simp [Retraction.toTopCatHom, TopCat.diskBoundaryInclusion, r.fixes_sphere p hsphere]` | **Failed**: `simp` reduced to `{ down := ⟨r.toFun p, _⟩ } = { down := ⟨p, hp⟩ }` but `r.fixes_sphere` was unused (no `r.toFun p` literally on either side after reduction) |
| 3 | `ext ⟨⟨p, hp⟩⟩` + `apply ULift.ext` + `apply Subtype.ext` + `exact r.fixes_sphere p hsphere` | **Built green** at 3309/3309, 64s warm |

The PREP §3.1 skeleton was right on the spec but the proof closure
needed Mathlib's `@[ext]` chain `ULift.ext` → `Subtype.ext`, not a
single `simp` call. Honest tagging: PREP "paste-ready but unverified"
qualifier was load-bearing — three iterations to close `section_identity`.

## 4. What this unblocks for S16 ACT-B

With G10 on main, the S16 ACT-B (main-file integration) can:

1. Add `import Proofs.BrouwerFixedPointOQ01OQ02G10` to the main file's
   import list.
2. Use `r.toTopCatHom` as the `ρ : 𝔻 n ⟶ ∂𝔻 n` argument to G8's
   `map_section_of_section`.
3. Use `r.section_identity` as the `h : i ≫ r = 𝟙 X` hypothesis to
   the same G8 call.

ACT-B still needs to:

* Close **Gap-2** (ULift mismatch between substantive ball/sphere):
  ship `H_n_minus_1_disk_zero_substantive` per S15 PREP §4.1 (~12 LOC).
* Decide the **n=1 branch** treatment (thin IVT axiom OR 5-line IVT
  proof) — see S15 PREP §5 final paragraph.
* Replace the mock axiom `H_n_minus_1_sphere_nonzero`
  (main:261) with the substantive theorem chaining G10 + G8 + G9 +
  `H_n_minus_1_disk_zero_substantive` + `H_n_minus_1_sphere_nonzero_substantive`.

Expected ACT-B build size: ~3300–3400 jobs per S15 PREP §7 (this
estimate is for the main-file rebuild, not the cumulative closure).

## 5. On-disk reality (this PR, 2026-06-01)

| File | LOC | Theorems | Definitions | Axioms | Sorries |
|------|-----|----------|-------------|--------|---------|
| `BrouwerFixedPointOQ01OQ02.lean` | 462 | 14 | … | 4 | 0 |
| `BrouwerFixedPointOQ01OQ02G6.lean` | 88 | 4 + 1 local | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G7.lean` | 94 | 2 | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G8.lean` | 134 | 2 | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G10.lean` | **78** | **1** | **1** | **0** | **0** |
| **Total** | **856** | **24** | … | **4** | **0** |

Net delta this PR: +78 LOC, +1 theorem, +1 definition, +0 axioms, +0 sorries.

## 6. Anti-targets (S16 ACT-A)

- No edits to `BrouwerFixedPointOQ01OQ02.lean` (Gap-2 / mock-axiom
  removal deferred to S16 ACT-B per the recommended split).
- No edits to G6/G7/G8 (already on main, build verified).
- No `meta.json` updates (slug has no gallery directory; verified
  `src/data/proofs/brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02/`
  does not exist).
- No upstream Mathlib contribution (B1 / B2 still on the queue).

## 7. Honesty notes

- The S15 PREP §7 build-cost estimate (~400–500 jobs) was **off by
  ~7×** — actual was 3309. Reason: `Mathlib.Topology.Category.TopCat.Sphere`'s
  import closure dominates. The PREP estimate looked only at G6/G7/G8
  deltas, none of which import Sphere. ACT-B's estimate (~3300–3400)
  remains plausible — it was based on the main-file rebuild, which
  also imports Sphere.
- The `section_identity` proof required three iterations to close.
  Two PREP-implicit assumptions failed: (a) the v4.26.0 ULift
  continuity lemma names are `continuous_uliftUp` / `continuous_uliftDown`,
  not `continuous_uLift_{up,down}` as the PREP wrote; (b) closing the
  ULift+Subtype equality needs explicit `ULift.ext` + `Subtype.ext`
  calls, not just `simp [Retraction.toTopCatHom, …]`. Both are
  cosmetic — the underlying spec is right.
- The PR does not retire any axiom from the main file. The mock
  axiom `H_n_minus_1_sphere_nonzero` is still live; its retirement
  is the ACT-B deliverable.
- Build-cost surprise (3309 vs 400–500 estimate) is recorded honestly
  here; the future ACT-B planner should expect ~3300–3400 for the
  full main-file rebuild including G10's import closure, not double-
  count G10's jobs.
