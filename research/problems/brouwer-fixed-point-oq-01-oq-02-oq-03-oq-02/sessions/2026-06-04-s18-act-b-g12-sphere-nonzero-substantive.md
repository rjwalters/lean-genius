# S18 ACT-B — G12 companion file (`H_n_minus_1_sphere_nonzero_for_retraction`)

- **Date**: 2026-06-04
- **Session**: 19 (S1–S17 + S13b BUILD-VERIFY-AND-FIX)
- **Phase**: ACT-B (delivers the categorical wire-up identified by S15
  PREP §5 as the payload of the main-file integration; main-file edit
  still deferred to S19 ACT-C)
- **Author**: researcher-7
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged)
- **Scope**: ships `proofs/Proofs/BrouwerFixedPointOQ01OQ02G12.lean`
  (single-theorem companion file, ~120 LOC including docstring) plus
  the `proofs/Proofs.lean` rollup catch-up (G12). No edits to main
  file, no edits to G6/G7/G8/G10/G11, no `axiom` delta, no `sorry`,
  no `meta.json` (slug has no gallery directory).

## 1. What this PR delivers

The S15 PREP §5 paste-ready integration body shipped as a fresh
companion file rather than as an in-line edit to the main file. Single
theorem in namespace `BrouwerOQ01OQ02`:

* **`H_n_minus_1_sphere_nonzero_for_retraction`** — for `n ≥ 2`, any
  `Retraction n`, and any `φ : ℤ →+ Unit`, there exists `ψ : Unit →+ ℤ`
  with `ψ.comp φ = AddMonoidHom.id ℤ`. Signature matches the mock
  axiom `H_n_minus_1_sphere_nonzero` (main:261) modulo the strengthened
  `n ≥ 2` hypothesis (mock uses `n ≥ 1`, with the `n = 1` case left to
  the future `Retraction_one_uninhabited` lemma per S15 PREP §5 /
  knowledge.md §G5).

The proof reaches the conclusion by `exfalso` after deriving the
substantive contradiction `IsZero (H_{n-1}(𝕊^{n-1}))` ⨯
`¬ IsZero (H_{n-1}(𝕊^{n-1}))` via the chain:

1. (G10) `Retraction.section_identity` gives
   `diskBoundaryInclusion n ≫ r.toTopCatHom = 𝟙 (∂𝔻 n)` in TopCat.
2. (G8) `map_section_of_section` transports the section through
   `F := (singularHomologyFunctor AddCommGrpCat.{0} (n-1)).obj (AddCommGrpCat.of ℤ)`.
3. (G11) `H_n_minus_1_disk_zero_substantive` gives `IsZero (F.obj 𝔻 n)`.
4. (G8) `isZero_of_section_into_isZero` combines (2) + (3) to derive
   `IsZero (F.obj ∂𝔻 n)`.
5. The main file's `H_n_minus_1_sphere_nonzero_substantive` (main:375)
   contradicts (4).

This closes the **categorical wire-up step** of the S9 ACT-D-3 EXEC
plan that S15 PREP §5 first sketched and S16/S17 ACT-A/ACT-B-PRE
pre-staged via G10/G11.

## 2. Docker build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G12
...
✔ [3312/3312] Built Proofs.BrouwerFixedPointOQ01OQ02G12 (14s)
Build completed successfully (3312 jobs).
=== Build succeeded ===
```

**3312 jobs**, ~14s wall for the G12 step itself (cold-cache total
wall ~3.5 min including Mathlib cache download via `lake exe cache get`).
Matches the G11 import-closure cost (3309 jobs) within ±3 jobs: G12 adds
no new Mathlib imports beyond G10/G11; the only extra inputs are in-repo
G8 declarations (`map_section_of_section`, `isZero_of_section_into_isZero`).

The build was preceded by a single false-start: the first attempt
attempted to build a host-mounted file `/workspace/proofs/Proofs/…G12.lean`
that did not exist inside the worktree (the file had been written to the
main-repo path by mistake). After moving to the worktree path and
re-running, the build succeeded on the first attempt.

## 3. What this does NOT do

This file does NOT remove the main file's `axiom H_n_minus_1_sphere_nonzero`
(line 261). That removal is the **S19 ACT-C** step: a single edit to
the main file changing `axiom` → `theorem` with a body that wraps the
G12 result for `n ≥ 2` and ships a thin local lemma
`Retraction_one_uninhabited` (IVT-based, knowledge.md §G5) for `n = 1`.

The split into G12 (this PR) + S19 ACT-C (the main-file edit) isolates
the substantive derivation from the main-file rebuild risk — the same
companion-file pattern that S13/S16/S17 used for G6/G10/G11.

## 4. Bearer audit (Mathlib v4.26.0 / SHA `2df2f0150c…`)

No new Mathlib bearers beyond what G10/G11 already pull in. The G12
proof body cites only in-repo bearers:

| Bearer | Source | Line | Used for |
|---|---|---|---|
| `BrouwerFixedPointOQ01OQ02.map_section_of_section` | `…G8.lean` | 92 | Functoriality of F on the section |
| `BrouwerFixedPointOQ01OQ02.isZero_of_section_into_isZero` | `…G8.lean` | 115 | Retract of zero is zero |
| `BrouwerOQ01OQ02.Retraction.toTopCatHom` | `…G10.lean` | 50 | TopCat morphism `𝔻 n ⟶ ∂𝔻 n` |
| `BrouwerOQ01OQ02.Retraction.section_identity` | `…G10.lean` | 73 | `i ≫ ρ = 𝟙` in TopCat |
| `BrouwerOQ01OQ02.H_n_minus_1_disk_zero_substantive` | `…G11.lean` | 67 | `IsZero (F.obj 𝔻 n)` |
| `BrouwerOQ01OQ02.H_n_minus_1_sphere_nonzero_substantive` | `…OQ02.lean` | 375 | `¬ IsZero (F.obj ∂𝔻 n)` |

All bearers are in-repo and on `origin/main`. No Mathlib API drift
re-check needed beyond what S17 ACT-B-PRE already discharged for G11.

## 5. Universe handling

The G12 body is universe-monomorphic at `.{0}`, matching the G10/G11
precedent. The main file's `H_n_minus_1_sphere_nonzero_substantive`
uses the bare form `TopCat.diskBoundary n` without explicit `.{0}`;
universe inference from the functor application disambiguates to
`.{0}`, so the contradiction step `H_n_minus_1_sphere_nonzero_substantive
n hn hSphereZ` unifies the universes via Lean's elaboration.

## 6. On-disk reality (this PR, 2026-06-04)

| File | LOC | Theorems | Definitions | Axioms | Sorries |
|------|-----|----------|-------------|--------|---------|
| `BrouwerFixedPointOQ01OQ02.lean` | 462 | 14 | … | 4 | 0 |
| `BrouwerFixedPointOQ01OQ02G6.lean` | 88 | 4 + 1 local | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G7.lean` | 94 | 2 | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G8.lean` | 134 | 2 | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G10.lean` | 78 | 1 | 1 | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G11.lean` | 73 | 1 | … | 0 | 0 |
| `BrouwerFixedPointOQ01OQ02G12.lean` | **126** | **1** | … | **0** | **0** |
| **Total** | **1055** | **26** | **1** | **4** | **0** |

Net delta this PR: +126 LOC, +1 theorem, +0 definitions, +0 axioms,
+0 sorries (plus +1 line in `Proofs.lean`).

## 7. What this unblocks for S19 ACT-C (main-file integration)

With G12 on main, the S19 ACT-C main-file edit reduces to:

1. Add 1 import: `import Proofs.BrouwerFixedPointOQ01OQ02G12`.
2. Change line 261 `axiom H_n_minus_1_sphere_nonzero …` to
   `theorem H_n_minus_1_sphere_nonzero (n : ℕ) (hn : n ≥ 1) (r : Retraction n)
       (φ : ℤ →+ Unit) : ∃ ψ : Unit →+ ℤ, ψ.comp φ = AddMonoidHom.id ℤ := by …`.
3. Body: `by_cases hn2 : 2 ≤ n` →
   - `case pos`: `exact H_n_minus_1_sphere_nonzero_for_retraction n hn2 r φ`.
   - `case neg`: handle `n = 1` via `Retraction_one_uninhabited` (IVT,
     knowledge.md §G5) — either a thin local axiom (net axiom 4 → 4)
     or a ~5-line IVT proof (net axiom 4 → 3).

Expected S19 build size: ~3300–3400 jobs (main-file rebuild + G12
import closure).

## 8. Anti-targets (S18 ACT-B)

- No edits to `BrouwerFixedPointOQ01OQ02.lean` (mock-axiom removal
  deferred to S19 ACT-C).
- No edits to G6/G7/G8/G10/G11 (already on main, build verified).
- No `meta.json` updates (slug has no gallery directory; verified
  `src/data/proofs/brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02/`
  does not exist).
- No `Retraction_one_uninhabited` introduction (deferred to S19 ACT-C
  so the n=1 design decision is made in the same PR that retires the
  mock axiom).
- No upstream Mathlib contribution (B1 / B2 still on the queue).

## 9. Honesty notes

- The mock axiom `H_n_minus_1_sphere_nonzero` (main:261) is still live
  after this PR. Net axiom delta: 0. The retirement is the S19 ACT-C
  deliverable; G12 only validates that the substantive derivation
  type-checks and builds clean before the main-file edit lands.
- The `n = 1` branch is still open in the same sense as it was at S17.
  G12 cleanly handles `n ≥ 2`; `n = 1` requires either an IVT proof of
  `Retraction 1` uninhabited (5 lines, dischargeable) or a thin local
  axiom (net 4 → 4 in axiom count).
- This PR follows the G6/G10/G11 companion-file precedent rather than
  doing the main-file edit in one shot. Reasons: (a) build-risk
  isolation — G12 builds in ~3300 jobs but if it fails, the main file
  is untouched; (b) review parallelism — G12 can be reviewed and
  merged independently of the S19 axiom-replacement PR; (c) the n=1
  design decision (axiom-vs-proof) is genuinely open and benefits from
  its own PR rather than being bundled into the integration.
