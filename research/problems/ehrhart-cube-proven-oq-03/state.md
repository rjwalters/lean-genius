# Research State: ehrhart-cube-proven-oq-03

## Current State

**Phase**: S2 PREP (bearer-audit, doc-only)
**Path**: full
**Since**: 2026-05-13T13:50Z (researcher-10, S2)
**Last Updated**: 2026-05-13 (Session 2 researcher-10)
**Iteration**: 2

## Session 2 — S2 PREP: Mathlib bearer audit + slot-drift discovery (researcher-10, 2026-05-13)

**Mode.** ANALYSIS-ONLY (no `.lean` edits; pure doc / JSON sync).

**Outcome.** The S1 OBSERVE plan (Session 1, 2026-05-12) is built on
**verifiably false premises** about Mathlib's Ehrhart-theory content,
and the slug's on-disk state has **drifted** from the JSON metadata.
Both must be corrected before any S2 ACT (Lean) iteration.

### Finding 1 — Mathlib has no Ehrhart theory

The S1 OBSERVE state.md claims:

> Mathlib v4.26.0 has Ehrhart theory in
> `Mathlib.Combinatorics.Polytope.Ehrhart` and rational-function /
> power-series infrastructure (`RatFunc`, `MvPowerSeries`, `MvPolynomial.aeval`).

This is **false** at the lake-pinned Mathlib SHA `2df2f0150c27`
(`proofs/lake-manifest.json`). Bearer audit via the GitHub Search API
returns:

| Query | Count |
|---|---|
| `Ehrhart` (any file, any path) | **0** |
| `Polytope` (any file, any path) | **0** |
| `LatticePolytope` (anywhere) | **0** |
| `hStar` / `h_star` / `Eulerian` (filename:Eulerian) | **0** |
| `Mathlib.Combinatorics.Polytope.Ehrhart` (direct fetch) | 404 |

Only the algebra dependencies are real:

| Module | Status | Size |
|---|---|---|
| `Mathlib.FieldTheory.RatFunc.Basic` | ✓ exists | 45 125 B |
| `Mathlib.Algebra.MvPolynomial.Basic` | ✓ exists | 41 370 B |
| `Mathlib.RingTheory.MvPowerSeries.Basic` | ✓ exists (path differs from S1 plan, which said `Mathlib.RingTheory.PowerSeries.Basic`) | n/a |

The S1 OBSERVE plan's "S2.1 Docker probe" would have flagged the
missing `Mathlib.Combinatorics.Polytope.Ehrhart` import on first
invocation. The bearer audit catches it without Docker (relevant given
the project-wide `proofs/.lake` self-referential-symlink trap in this
worktree).

**Implication.** Any retargeted S2 ACT toward Barvinok / generating
functions must build the Ehrhart support from scratch over Mathlib's
algebraic substrate (`RatFunc` / `MvPowerSeries` / `MvPolynomial`) —
there is no pre-existing Ehrhart toolkit to specialise.

### Finding 2 — Slug slot is already taken

`proofs/Proofs/EhrhartCubeProvenOQ03.lean` is **already on main**:

* Path `proofs/Proofs/EhrhartCubeProvenOQ03.lean` — 119 LOC, 6
  theorems, 2 definitions, 2 sorries, 0 axioms.
* Subject: **Hypersimplex** Δ(d, k) lattice-point counting (the slice
  of [0, 1]^d by the affine hyperplane Σ x_i = k), NOT Barvinok.
* `namespace EhrhartCubeProvenOQ03`.
* First committed in PR #18293 (`research(ehrhart-cube-proven-oq-03):
  S1 OBSERVE — hypersimplex Δ(d,k) Lean scaffold (build pending)`).
* `src/data/proofs/ehrhart-cube-proven-oq-03/` gallery directory
  exists with `meta.json` (title "Ehrhart Polynomial of the
  Hypersimplex: First-Principles Scaffold", `status: formalized`,
  `sorries: 2`, `badge: formalized`) + `annotations.json` + `index.ts`.

### Finding 3 — JSON `leanFiles` is empty despite on-main file

`src/data/research/problems/ehrhart-cube-proven-oq-03.json` reports
`leanFiles: []`. Reality: the hypersimplex file exists with 119 LOC.

### Finding 4 — Title / scope drift

| Field | JSON value | meta.json value (on-main) |
|---|---|---|
| `title` | "Barvinok's algorithm for lattice point counting in fixed dimension" | "Ehrhart Polynomial of the Hypersimplex: First-Principles Scaffold" |
| `tags` includes | `barvinok`, `algorithms` | `hypersimplex`, `open-problem` |

The Session 1 (2026-05-12) iteration **retargeted the slug from
hypersimplex to Barvinok without touching the on-main scaffold** or
the gallery entry. The slot now holds two incompatible plans.

## Recommended Continuation Paths

Two clean options, surfaced for seeker / curator / human triage —
this PR does **not** decide between them:

### Option A — Continue the hypersimplex track (low-risk)

Treat the slug as `ehrhart-cube-proven-oq-03` ⇔ hypersimplex Δ(d, k)
(matches on-main scaffold + gallery + meta.json). S3 next:

1. Discharge `hypersimplex_count_k_one`: Δ(d, 1) lattice count
   = C(n + d − 1, d − 1) via the multiset-stars-and-bars bijection.
2. Discharge `hypersimplex_palindrome_k_d_minus_1`: Δ(d, k) count
   = Δ(d, d − k) count via the involution x ↦ n − x.

Both proofs are tractable in Mathlib v4.26.0 (use `Fintype.card`,
`Finset.bij`, `Finset.sum`); ~70 LOC each. Pure combinatorics, no
algebraic-geometry preliminaries.

### Option B — Retarget to a new sibling slug `oq-05` (Barvinok)

Spin off the Barvinok-1994 plan as **`ehrhart-cube-proven-oq-05`**
(or `-oq-06`; current siblings end at -04). That slug starts with the
correct Mathlib substrate awareness from this audit and does not
collide with the hypersimplex slot. The Session 1 S1 OBSERVE
documentation (problem.md + knowledge.md + Barvinok plan) becomes the
new slug's bootstrap; `ehrhart-cube-proven-oq-03` reverts to its
on-main hypersimplex identity.

## Decision: deferred

This PR ships **bearer-audit findings + JSON drift fixes only**.
Scope decision (Option A vs B) deferred to seeker / curator / human
triage.

## Files modified (this PR)

* `research/problems/ehrhart-cube-proven-oq-03/state.md` — this file.
* `research/problems/ehrhart-cube-proven-oq-03/knowledge.md` — append
  bearer-audit section.
* `src/data/research/problems/ehrhart-cube-proven-oq-03.json` — phase
  S1_OBSERVE → S2_PREP, iteration 1 → 2, `lastUpdate`, `knownResults`
  (remove false Mathlib claim), `currentState.{focus,nextAction}`,
  `knowledge.{progressSummary,insights,mathlibGaps,nextSteps}`,
  `references.mathlib` (correct paths), `references.urls` (remove dead
  Mathlib doc URL), `leanFiles` (add on-main hypersimplex entry).

## Out of scope (this PR)

* No `.lean` edits. The on-main hypersimplex scaffold is untouched.
* No retitle of the JSON `title` field — that is the scope-decision
  question deferred to Option A / B triage.
* No gallery `meta.json` edits — those describe the on-main scaffold
  accurately and would be modified by Option B only.
* No new sibling slug creation — seeker / curator can spin off
  `oq-05` if Option B is chosen.

## Decision Log

* **2026-05-13 S2 (researcher-10)**: Decision to ship S2 as a
  doc-only PREP rather than S2 ACT. Reason: the S1 ACT plan
  ("S2.1 probe + S2.2 implement Barvinok scaffold") is built on the
  false `Mathlib.Combinatorics.Polytope.Ehrhart` premise AND would
  collide with the already-committed hypersimplex scaffold; both
  must be triaged first.
* **2026-05-13 S2 (researcher-10)**: Decision NOT to decide between
  Option A (continue hypersimplex) and Option B (spin off `oq-05`).
  Reason: scope decisions of this magnitude (rewriting the slug
  subject) should be made by the seeker / curator / human, not by a
  research iteration.
