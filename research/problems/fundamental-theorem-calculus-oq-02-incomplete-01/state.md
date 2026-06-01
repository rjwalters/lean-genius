# Research State: fundamental-theorem-calculus-oq-02-incomplete-01

## Current State

**Phase**: OBSERVE (S2 substantive — Mathlib survey + parent coverage + gap analysis shipped; ORIENT next)
**Path**: full
**Since**: 2026-06-01T09:50:00Z (S2 OBSERVE substantive iteration)
**Iteration**: 2

## Iteration 2 (researcher-1, 2026-06-01) — S2 OBSERVE: Mathlib v4.26.0 survey + parent-slug coverage + n-dim Stokes gap analysis (doc-only)

**Outcome**: OBSERVE complete. Slug moves from template-stub
iter 1 (2026-04-03 creation) to substantive scope. Mathlib state
surveyed; parent slug (`fundamental-theorem-calculus-oq-02`)
coverage mapped (1D Stokes-as-FTC + 2D rectangles via Green's + 2D
`d²=0` via Schwarz; 0 sorries 0 axioms in 395 LOC / 13 theorems);
n-dimensional Stokes gap precisely identified. The problem.md
target symbol `ContDiff.isSymmetric_iteratedFDeriv` **does NOT
exist in Mathlib v4.26.0** — this is a Mathlib gap, not a
re-statement task.

### What's in Mathlib v4.26.0 (foundations sufficient for ORIENT)

| Component | Status |
|---|---|
| `ModelWithCorners`, `IsInteriorPoint`, `IsBoundaryPoint`, `interior_union_boundary_eq_univ`, `boundary_eq_complement_interior` | ✅ Full API at `Mathlib/Geometry/Manifold/{SmoothManifoldWithCorners,InteriorBoundary}.lean` |
| `ContMDiff` / `MFDeriv` (manifold derivatives) | ✅ 6+ files under `Mathlib/Geometry/Manifold/MFDeriv/` |
| `AlternatingMap` (algebraic + topological) | ✅ `Mathlib/{LinearAlgebra/Alternating,Topology/Algebra/Module/Alternating}/Basic.lean` |
| `ExteriorAlgebra` | ✅ `Mathlib/LinearAlgebra/ExteriorAlgebra/{Basic,OfAlternating}.lean` |
| 2D Schwarz: `second_derivative_symmetric`, `Convex.second_derivative_within_at_symmetric` | ✅ `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`:303/315/254 |
| `iteratedFDeriv` API | ✅ `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean` |

### What Mathlib v4.26.0 LACKS (the gap)

| Missing | Workaround / next step |
|---|---|
| n-dim Schwarz `iteratedFDeriv_symmetric` | Induct on `n` from `second_derivative_symmetric` — **Fragment 1, 30-60 LOC**, Mathlib upstream-prep candidate |
| `DifferentialForm M k` on smooth manifold | Define via `AlternatingMap ℝ (TangentSpace I p) ℝ k` — **Fragment 2, 100-200 LOC**, multi-session PREP |
| Exterior derivative `d` | Chart-local; ~80-150 LOC — **Fragment 3** |
| Manifold integration `∫_M ω` | Partition-of-unity from `Mathlib/Geometry/Manifold/BumpFunction.lean` — **Fragment 4, 150-300 LOC, HIGH risk** |
| Boundary integration `∫_{∂M} ω` | Restrict via `I.boundary M` — **Fragment 5, 100-200 LOC, HIGH risk** |
| Generalized Stokes statement + proof | **Fragment 6+, 300-600 LOC, VERY HIGH risk** |

**Total scope**: ~800-1500 LOC across 15-30 sessions — comparable
to a Mathlib split-PR like `mathlib4#7967`. Multi-month research
track, not single-session.

### Tractability re-assessment

problem.md rates Tractability 5/10. S2 endorses the original
rating with the caveat that the goal must be **decomposed**: a
monolithic "complete the generalized Stokes theorem" formulation
is single-PR-infeasible at v4.26.0. The decomposition into 6
fragments (S2 §3.2 + §4) makes individual fragments single-PR
shippable, with Fragment 1 being the smallest-and-immediate
Mathlib-upstream-prep candidate.

### Next Action (S3 ORIENT)

**Preferred**: Fragment 1 ORIENT — investigate
`iteratedFDeriv_symmetric` proof skeleton. Read existing 2D
proof in `Symmetric.lean`:303/315; sketch the induction-on-`n`
argument; estimate LOC; identify Mathlib peer reviewers.

**Alternative S3 picks**:
* Literature scout: `gh pr list --repo leanprover-community/mathlib4
  --search "differential form|smooth manifold integration"` to
  check for in-flight Mathlib work on Fragments 2-5.
* Adjacent gallery slug discovery: search for any slug that has
  already formalized Lee's `Smooth Manifolds` exterior-derivative
  chapter.
* Pivot to a different slug (e.g., a sibling `fundamental-theorem-
  calculus-*` slug) if this one's scope is judged infeasible for
  the current researcher pool throughput.

**RECOMMENDATION**: S3 Fragment 1 ORIENT. Smallest-shippable scope
with independent upstream value.

### INFRA status (post-S50 cross-slug propagation)

| ID | Gate | Status |
|---|---|---|
| G7 | Disk | container-mode obsoletes |
| G8 | Docker daemon | 29.4.1 GREEN |
| G9 | `proofs/.lake` self-loop | RED but INERT for Docker `-v` bind-mount (4-slug confirmed) |

INFRA fully GREEN. S2 itself does not attempt any build (doc-only).

### Files modified (S2 doc-only)

* `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/state.md` — replaces template-stub with substantive S2 head.
* `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/sessions/2026-06-01-s2-observe-mathlib-survey-and-gap-analysis.md` (new, ~250 LOC, 10 sections).
* `src/data/research/problems/fundamental-theorem-calculus-oq-02-incomplete-01.json` — `currentState.iteration` 1 → 2, `lastUpdate` 2026-04-03 → 2026-06-01T09:50Z, `focus` + `nextAction` populated, `attemptCounts.total` 0 → 1.

### Counts (no Lean file authored yet)

* Parent slug `FundamentalTheoremCalculusStokes.lean`: 395 LOC, 13 thm, 0 sorries, 0 axioms (unchanged).
* This slug: no own Lean file yet (will be created at S3 ORIENT or S4 PREP / ACT, depending on Fragment-1 path).

### Memory pattern

This is a baseline pattern for first-substantive OBSERVE on deep
open problems: read problem.md + parent-slug meta + Mathlib state
survey + tractability decomposition + ORIENT plan, all in one
doc-only iteration. Future researchers claiming this slug should
read this S2 session document to skip the survey work.

---

## (Historic) Iteration 1 (2026-04-03 — auto-created from template, no substantive work)

**Phase**: OBSERVE  
**Path**: full  
**Since**: 2026-04-03T02:25:34-07:00  
**Iteration**: 1

Template-stub state from slug creation. Focus: "Initial problem
understanding. Read problem.md and gather context." Next action:
"Read problem.md thoroughly and acquire full context. Then move to
ORIENT phase to explore literature and related proofs."

No Lean file authored. No edits beyond auto-creation. T+59d gap
between iter 1 and iter 2.
