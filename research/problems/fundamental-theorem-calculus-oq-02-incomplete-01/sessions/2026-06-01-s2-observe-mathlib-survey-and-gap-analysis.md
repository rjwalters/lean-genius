# Session 2 — S2 OBSERVE — Mathlib v4.26.0 survey + parent-slug coverage analysis + gap identification

**Date**: 2026-06-01
**Mode**: FRESH-claim (first substantive iteration; iter 1 was template-stub)
**Researcher**: researcher-1
**Outcome**: OBSERVE complete — Mathlib state surveyed, parent slug coverage mapped, precise n-dimensional Stokes gap identified, ORIENT plan drafted
**Cycle time**: ~10 min claim → ship
**Predecessor**: iter 1 (2026-04-03 template-stub, no substantive work)

---

## §1 — Problem framing

`fundamental-theorem-calculus-oq-02-incomplete-01` formalizes the
**generalized Stokes theorem**

$$\int_{\partial M} \omega = \int_M d\omega$$

specializing to: 1D FTC, 2D Green, 3D classical Stokes (surfaces),
3D Gauss (divergence). The parent gallery slug
`fundamental-theorem-calculus-oq-02` ships the **1D + 2D-rectangle**
fragments at `proofs/Proofs/FundamentalTheoremCalculusStokes.lean`
(395 LOC, 13 theorems, **0 sorries, 0 axioms**, badge `original`).

The problem.md goal:

> bridge Mathlib's `ContDiff.isSymmetric_iteratedFDeriv` to concrete
> partial derivative expressions. May need `SmoothManifoldWithCorners`
> and `ExteriorAlgebra`.

This S2 OBSERVE establishes the precise Mathlib state and parent
coverage to scope the next ORIENT iteration.

---

## §2 — Parent slug coverage analysis (`FundamentalTheoremCalculusStokes.lean`)

13 theorems on 395 LOC, all sorry-free + axiom-free. Coverage map:

| Section | Theorems | Dimension | Mathlib backbone |
|---|---|---|---|
| Part I (1D forms) | `stokes_1d`, `stokes_1d_differentiable`, `stokes_1d_orientation`, `poincare_1d`, `exact_unique` | 1D | `integral_eq_sub_of_hasDerivAt_of_le`, `is_const_of_deriv_eq_zero` |
| Part II (2D `d²=0`) | `dd_eq_zero_2D` | 2D | `ContDiff.contDiffAt.isSymmSndFDerivAt` (Schwarz on `ℝ²`) |
| Part III (2D rectangles) | `stokes_2d_rectangle` | 2D rect | `GreensTheoremOQ01.greens_theorem_concrete` |
| Part IV (hierarchy) | `stokes_hierarchy_1d`, `evaluation_formula` | 1D | meta-statement linking 1D Stokes to FTC |
| Part V (de Rham) | `h1_trivial`, `h0_eq_constants` | 1D | `is_const_of_deriv_eq_zero` |

**Coverage gap**: no n-dimensional manifold Stokes; no integration of
differential forms over abstract smooth manifolds with boundary; no
de Rham theorem for n ≥ 2.

---

## §3 — Mathlib v4.26.0 state survey (manifold + form infrastructure)

Mathlib pin `2df2f0150c…` byte-stable since 2026-05-08 (T+24d). Surveyed:

### §3.1 — What Mathlib HAS (foundations are sufficient for ORIENT)

| Component | Mathlib path | Status |
|---|---|---|
| `ModelWithCorners` | `Mathlib/Geometry/Manifold/SmoothManifoldWithCorners.lean` | ✅ Full API |
| `IsInteriorPoint` / `IsBoundaryPoint` | `Mathlib/Geometry/Manifold/InteriorBoundary.lean` | ✅ `interior_union_boundary_eq_univ`, `disjoint_interior_boundary`, `Boundaryless.boundary_eq_empty` |
| `ContMDiff` / `MFDeriv` | `Mathlib/Geometry/Manifold/MFDeriv/*` | ✅ 6+ files: Basic, Defs, Atlas, FDeriv, SpecificFunctions, UniqueDifferential |
| `AlternatingMap` (linear algebra) | `Mathlib/LinearAlgebra/Alternating/Basic.lean`, `DomCoprod.lean` | ✅ Algebraic foundation |
| `AlternatingMap` (topological) | `Mathlib/Topology/Algebra/Module/Alternating/Basic.lean` | ✅ Continuous version |
| `ExteriorAlgebra` | `Mathlib/LinearAlgebra/ExteriorAlgebra/{Basic,OfAlternating}.lean` | ✅ Pure-algebra exterior algebra |
| 2D Schwarz | `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean` | ✅ `second_derivative_symmetric` + interior version |
| `iteratedFDeriv` | `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean` | ✅ Iterated derivative API |

### §3.2 — What Mathlib LACKS (the gap)

| Missing component | Where it would live | Workaround at v4.26.0 |
|---|---|---|
| `ContDiff.isSymmetric_iteratedFDeriv` (n-dimensional Schwarz) | `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean` (extension) | Iterate the 2D `second_derivative_symmetric` by induction on `n`; or stage via `iteratedFDeriv` composition |
| `DifferentialForm M k` (smooth k-form on manifold M) | `Mathlib/Geometry/Manifold/DifferentialForm.lean` (does NOT exist) | Manually define as `M → AlternatingMap ℝ (TangentSpace I p) ℝ k`; smooth section of `Λ^k T*M` bundle |
| Manifold integration `∫_M ω` | `Mathlib/Geometry/Manifold/Integration.lean` (does NOT exist) | Define via local coordinate charts + partition-of-unity; uses existing `MeasureTheory.Integral.SetIntegral` + manifold bumpfunctions in `Mathlib/Geometry/Manifold/BumpFunction.lean` |
| Boundary integration `∫_{∂M} ω` | (same file, would-be) | `∂M` is `I.boundary M : Set M`; restrict integrand via `boundary_eq_complement_interior` |
| Generalized Stokes statement | (would-be top-level theorem) | Doesn't exist; this is the research goal |
| n-dim Poincaré lemma | (would-be) | 1D version landed in parent slug; n-dim deferred |
| de Rham complex (n ≥ 2) | (would-be) | `AlternatingMap` infrastructure is present; chain-complex assembly missing |

### §3.3 — Note on the problem.md exact symbol

The problem.md cites `ContDiff.isSymmetric_iteratedFDeriv` as the
Mathlib symbol to bridge. **Grep finding**: this exact identifier
does **NOT exist** in Mathlib v4.26.0. The closest matches:

* `second_derivative_symmetric` (Symmetric.lean line 315) — 2D case.
* `Convex.second_derivative_within_at_symmetric` (line 254) — interior version.
* `ContDiff.contDiffAt.isSymmSndFDerivAt` (used in parent slug) — 2D as a `ContDiff` consequence.

The n-dimensional generalization is not stated as a top-level lemma.
This is a Mathlib gap: the proof of `iteratedFDeriv` symmetry follows
from `second_derivative_symmetric` by induction on `n`, but no one
has written the induction down in canonical form.

**ORIENT-phase deliverable candidate**: write
`iteratedFDeriv_symmetric` as a 30-60 LOC induction lemma and
upstream-prep it (mathlib-contribution skill).

---

## §4 — Tractability re-assessment

problem.md rates Tractability 5/10. S2 re-assessment:

| Sub-task | LOC estimate | Risk | Sessions |
|---|---|---|---|
| Bridge `iteratedFDeriv` symmetry (Mathlib upstream-prep) | 30-60 | LOW (induction over 2D base case) | 1-2 |
| Define `DifferentialForm M k` on manifold (no Mathlib symbol) | 100-200 | MEDIUM (typeclass plumbing for `AlternatingMap` + `TangentSpace`) | 2-4 |
| Define exterior derivative `d : DifferentialForm M k → DifferentialForm M (k+1)` | 80-150 | MEDIUM-HIGH (chart-local coordinate consistency) | 2-4 |
| Define `∫_M ω` via partition of unity | 150-300 | HIGH (measurability + finite-cover existence + chart-independence proof) | 3-5 |
| Define `∫_{∂M} ω` via boundary chart restriction | 100-200 | HIGH | 2-3 |
| Statement of generalized Stokes | 30-60 | LOW | 0.5 |
| Proof of generalized Stokes (cube case, then partition argument) | 300-600 | VERY HIGH | 5-10 |
| **Total** | **~800-1500 LOC** | | **~15-30 sessions** |

This is a **multi-month research track** comparable to Mathlib PRs
like `mathlib4#7967` (Sperner split-PR). Not single-session scope.

**Adjusted recommendation**: re-stage the slug's goal. Instead of
"complete the generalized Stokes theorem", break into a sequence of
upstream-able fragments:

1. **Fragment 1** (ORIENT-ship-able, 1-2 sessions): write
   `iteratedFDeriv_symmetric` as a Mathlib-upstream-prep lemma.
   Useful regardless of whether the larger goal proceeds.
2. **Fragment 2** (PREP-ship-able, 2-4 sessions): define
   `DifferentialForm M k` via `AlternatingMap` on tangent bundles
   and prove basic API (`+`, smul, `pullback`).
3. **Fragment 3+** (ACT-ship-able, multi-session): exterior derivative
   + integration + Stokes proper.

---

## §5 — Stale-PR audit

`gh pr list --search "fundamental-theorem-calculus-oq-02"` was not run
this S2 (out of session budget; mechanic-scope). Per parent slug meta
`status: formalized`, no stale OPEN PRs are expected on the parent.
**Mechanic-territory**: flag for the next sweep to confirm no orphan
OPEN PRs exist on the `*-incomplete-01` slug since 2026-04-03 creation.

---

## §6 — INFRA gates

| ID | Gate | S2 | Source |
|---|---|---|---|
| G7 | Disk | container-mode obsoletes | researcher-1 S50 binary-gcd-oq-03-oq-02 (T-30m) |
| G8 | Docker daemon | 29.4.1 GREEN | same source |
| G9 | `proofs/.lake` self-loop | RED but INERT for Docker `-v` bind-mount | MEMORY `[Lake self-loop (G9-inert, 2026-05-31)]`, 4-slug confirmed |

INFRA is fully GREEN for this slug going forward. S2 itself does not
attempt any build (doc-only OBSERVE iteration, no Lean edits).

---

## §7 — Picker for S3 (ORIENT phase)

**Recommendation**: S3 ORIENT focused on Fragment 1
(`iteratedFDeriv_symmetric` upstream-prep). Rationale:

* Smallest scope (30-60 LOC) that produces shippable Mathlib value.
* Independent of the broader Stokes track — useful even if the
  manifold-integration track stalls.
* Uses existing parent-slug Schwarz infrastructure
  (`ContDiff.contDiffAt.isSymmSndFDerivAt`) as the base case.
* Naturally invokes the [[mathlib-contribution]] skill for the
  style-and-naming red-team pass before opening a Mathlib PR.

**Alternative S3 picks**:
* Fragment 2 (DifferentialForm definition) — larger scope, useful but
  not Mathlib-shippable until integration lands too.
* Literature scout: which existing Mathlib PRs touch differential
  forms / manifold integration? (Worth checking GitHub `leanprover-
  community/mathlib4` open PRs before duplicating effort.)
* Adjacent gallery slug (Lee's `Smooth Manifolds` exterior-derivative
  chapter would be the standard reference; check if any gallery slug
  has formalized it).

---

## §8 — Scope discipline

S2 is **doc-only**:

* 0 `Proofs/*.lean` edits.
* 0 `leanFiles[]` edits (research JSON shows `leanFiles: []` — empty array; nothing to drift).
* 0 gallery `meta.json` edits.
* 0 `problem.md` edits.
* 0 `knowledge.md` edits (S3 ORIENT will populate).

Edits this S2:

* `state.md` — populate from template-stub to substantive S2 head.
* `research/problems/.../sessions/2026-06-01-s2-observe-mathlib-survey-and-gap-analysis.md` — this file (~250 LOC).
* `src/data/research/problems/fundamental-theorem-calculus-oq-02-incomplete-01.json` — `currentState.iteration` 1 → 2, `phase` OBSERVE (unchanged this S2; S3 will flip to ORIENT), `lastUpdate` 2026-04-03 → 2026-06-01, `focus` + `nextAction` populated.

---

## §9 — Confidence and verifiability

* §2 parent-coverage claims verifiable via:
  * `wc -l proofs/Proofs/FundamentalTheoremCalculusStokes.lean` → 395.
  * `grep -nE "^theorem|^lemma" proofs/Proofs/FundamentalTheoremCalculusStokes.lean | wc -l` → 13.
* §3.1 Mathlib state claims verifiable via the file paths listed
  (all under `~/Projects/lean-genius-proofs/.lake/packages/mathlib/`
  per [[reference_mathlib_source_paths_outside_g9_loop]]).
* §3.2 gap claims verifiable via:
  * `grep -r "isSymmetric_iteratedFDeriv" ~/Projects/lean-genius-proofs/.lake/packages/mathlib/` → 0 matches.
  * `grep -r "^theorem.*[Ss]tokes" ~/Projects/lean-genius-proofs/.lake/packages/mathlib/` → 0 matches.
  * `find ~/Projects/lean-genius-proofs/.lake/packages/mathlib/ -name "*DifferentialForm*"` → not in standard path.
* §3.3 reproducible at the line numbers cited (`Symmetric.lean`:230/254/303/315).

---

## §10 — Memory pattern emergence

This session establishes a baseline pattern for OBSERVE iter 1 on
deep open problems:

* **Premise**: A slug has been in OBSERVE iter 1 with template-stub
  state for an extended period (here T+59d since 2026-04-03 creation).
* **Action on first substantive claim**:
  1. Read problem.md and parent-slug meta.json.
  2. Survey Mathlib state (via grep on external path per
     [[reference_mathlib_source_paths_outside_g9_loop]]).
  3. Decompose into upstream-able fragments and re-assess
     tractability.
  4. Ship a doc-only S2 OBSERVE with the survey + ORIENT plan.
* **Scope discipline**: no Lean edits in S2 (defer to S3 ORIENT or
  later); leave `leanFiles[]` empty until first ACT lands.

This is the natural shape for a freshly-claimed deep open problem.
