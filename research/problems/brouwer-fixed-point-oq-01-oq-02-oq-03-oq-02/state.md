# Current State

**Phase**: ACT (S8 ACT-D-2 DESIGN complete, doc-only; S8 ACT-D-2 EXEC pending)
**Since**: 2026-05-13 (Session 8, researcher-4, design half of S8)
**Iteration**: 8

## Current Focus

S8 ACT-D-2 DESIGN (this session, researcher-4, 2026-05-13,
**doc-only**) — fixes the exact Lean signature, import list,
Mathlib API survey, two-stage proof sketch, companion-file
layout, S9/S10 integration plan, build-risk analysis, and EXEC
checklist for the **G7 algebraic bridge**

    ¬ IsZero (X : AddCommGrpCat) → ∃ x : X.carrier, x ≠ 0

so that the S8 ACT-D-2 EXEC follow-on session can install the
companion file `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean`
(target: 20–30 lines, 2 small theorems) without further
specification work.

Lean changes this iteration: **none** (doc-only). Net axiom delta:
0. Net theorem delta: 0. File-level counts unchanged at 14
theorems / 4 axioms / 0 sorries.

Full design in `knowledge.md` Section N (sub-sections N1–N9):

* **N1**: target signature `AddCommGrpCat.exists_ne_zero_of_not_isZero`
  (universe-monomorphic at `Type 0` to match existing call sites)
  plus the stronger `iff` form `AddCommGrpCat.not_isZero_iff_nontrivial`.
* **N2**: 4 imports — `Algebra.Category.Grp.Basic`,
  `Algebra.Category.Grp.Zero`, `CategoryTheory.Limits.Shapes.ZeroObjects`,
  `Logic.Nontrivial.Basic`. Strict subset of the main file's import
  list; no `Topology.*` / `AlgebraicTopology.*` deps.
* **N3**: Mathlib API survey at pinned rev `v4.26.0`. Three required
  facts; two verified, one flagged for 1-minute grep at EXEC start
  (`AddCommGrpCat.isZero_iff`-style name). 10-line inline fallback
  if the flagged lemma is renamed.
* **N4**: two-stage proof sketch (`iff` lemma + existential
  corollary, total ~20–30 Lean lines).
* **N5**: companion-file installation (Option A, recommended) vs
  inline-in-main-file (Option B). Option A preferred for build-risk
  isolation and review parallelism.
* **N6**: integration with S9 ACT-D-3 (gated on sibling PR #18011)
  and S10 ACT-D-4 (mock-axiom drop). No cyclic-import risk.
* **N7**: 3 build-risk factors, each with ≤ 10-line inline
  fallback. Overall build-risk lower than S5 ACT-B, comparable
  to S7 ACT-D-1.
* **N8**: 8-step EXEC checklist for the follow-on session.

## Historical Focus (S7 ACT-D-1 exec, PR #18168, build verified)

S7 ACT-D-1 exec — install the **thin B2 surrogate axiom**
`sphere_singularHomology_nonzero` (candidate-(a) from §L4) and the
**trivial substantive theorem** `H_n_minus_1_sphere_nonzero_substantive`
(from §L5) into `proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean`,
mirroring the ball-side `contractible_singularHomology_zero` /
`H_n_minus_1_ball_zero_substantive` pair landed in S5 ACT-B exec
(PR #18018).

Lean changes: +1 import (`Mathlib.Topology.Category.TopCat.Sphere`),
+1 axiom (`sphere_singularHomology_nonzero`), +1 theorem
(`H_n_minus_1_sphere_nonzero_substantive`), +1 docstring section.
Net axiom delta: +1 (file-level count 3 → 4). Net theorem delta: +1
(13 → 14).

## Active Approach

S7 ACT-D-1 installation summary:

  1. **Sphere import added**. Line 10:
     `import Mathlib.Topology.Category.TopCat.Sphere`. This pulls in
     `TopCat.disk`, `TopCat.diskBoundary`, `TopCat.sphere`,
     `TopCat.ball` with their `ULift`-wrapped `EuclideanSpace`
     definitions (verified at pinned rev, see §L1).

  2. **Axiom `sphere_singularHomology_nonzero`** installed between
     `H_n_minus_1_ball_zero_substantive` and
     `singular_homology_retraction_split`. Exact signature matches
     §L4 candidate-(a): `(n : ℕ) (hn : 1 ≤ n) : ¬ IsZero (H_n (𝕊 n))`,
     using `TopCat.diskBoundary (n + 1)` for the carrier
     (`TopCat.sphere n = TopCat.diskBoundary (n + 1)` by definition,
     so the two forms are definitionally equal).

  3. **Theorem `H_n_minus_1_sphere_nonzero_substantive`** installed
     immediately below the axiom. The proof is the obvious
     `(n - 1) + 1 = n` index-shift (proved by `omega`) followed by a
     `rw` and an `exact`. No typeclass-synthesis chain, no manifold
     instances. Hypothesis `2 ≤ n` ensures `1 ≤ n - 1` for the axiom
     application (§L5 boundary-case note carried over verbatim).

  4. **File header docstring** updated to reflect the new theorem
     count and new axiom count, with a `## S7 ACT-D-1 exec (2026-05-12)`
     section describing the surrogate / substantive pair, the net
     deltas, and the upstream contribution path.

  5. **knowledge.md Section L7 ACT-D execution plan**: S7 step now
     EXECUTED. §M (new section, this iteration) documents the
     installation: file-level axiom count is now 4
     (no_retraction_axiom, H_n_minus_1_sphere_nonzero,
     contractible_singularHomology_zero,
     sphere_singularHomology_nonzero), all four with explicit Mathlib
     contribution paths.

Net effect on Lean codebase: +1 axiom + 1 theorem + 1 import. Build
verified (see PR description for build-log reference). The
`Retraction`-quantifier mock axiom `H_n_minus_1_sphere_nonzero`
remains in place; dropping it is deferred to S10 ACT-D-4 after the
G7 algebraic bridge (S8) and the G6 functoriality bridge (S9, gated
on sibling PR #18011) are in place.

## Blockers

* **B1 (Mathlib gap)** — prism operator still missing. Encoded as
  the thin local axiom `contractible_singularHomology_zero` (S5
  ACT-B exec). Upstream contribution path is mapped (Section H).
* **B2 (Mathlib gap)** — `H_n(𝕊 n) ≠ 0` now encoded as the thin
  local axiom `sphere_singularHomology_nonzero` (this iteration).
  Upstream contribution path via the cellular chain complex of
  `𝕊 n` (Section L3 / B2-CW), with `TopCat.diskBoundary`
  providing the canonical signatures.
* **G7 (algebraic bridge, sphere side)** — the substantive theorem
  produces `¬ IsZero (...)` whereas the downstream consumer
  `H_n_minus_1_sphere_nonzero` expects `∃ ψ, ψ ∘ φ = id`. The G7
  bridge (`¬ IsZero (X) → ∃ x : X, x ≠ 0` for `AddCommGrpCat`) is
  self-contained algebra and is the next item on the ACT-D track
  (S8 ACT-D-2).
* **Sibling PR #18011 (G6 Unit-bridge)** still OPEN. S9 ACT-D-3
  depends on its merge for the subsingleton-bridge half. Until
  then, the sphere-side substantive theorem exists as a
  parallel-but-not-yet-bridged structure.

## Next Action

**S8 ACT-D-2 EXEC (immediate next, recommended)**: install the
companion file `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean`
per `knowledge.md` §N5 Option A, executing the 8-step checklist
in §N8. The design (this iteration) has fixed:

  * Exact Lean signature (§N1) — two theorems
    `AddCommGrpCat.exists_ne_zero_of_not_isZero` and
    `AddCommGrpCat.not_isZero_iff_nontrivial`.
  * Imports (§N2) — 4 lines, strict subset of main file.
  * Proof body (§N4) — two-stage, ~20–30 lines total.
  * API-verification grep (§N7 risk 1) — 1 minute at EXEC start.
  * Fallback constructions for all 3 build-risks — ≤ 10 lines each.

Target Lean delta: +1 file (companion), +2 theorems, +0 axioms,
+0 sorries. Build-risk: comparable to S7. Estimate: 1 session.

**S9 ACT-D-3 (after PR #18011 merges)**: combine the S8 G7 bridge
with functoriality + G6 (PR #18011's Part VI Subsingleton-bridge)
to bridge `¬ IsZero (H_{n-1}(𝕊 (n-1)))` to the existential
`∃ ψ : Unit →+ ℤ, ψ ∘ φ = id`. This is the step that *replaces*
the mock axiom `H_n_minus_1_sphere_nonzero` with a substantive
derivation.

**S10 ACT-D-4 (after S9)**: drop the mock axiom
`H_n_minus_1_sphere_nonzero` entirely; rewire
`singular_homology_retraction_split` to use the substantive chain.
Net axiom delta: −1 (file-level count 4 → 3, back to "all surrogates
are textbook facts").

**Deferred to S11+**: full Mathlib B1/B2 upstream contributions
(see Section H for B1, Section L3 / B2-CW for B2). These are
independent of the gallery proof and can proceed in parallel.

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 1 (S8 ACT-D-2 DESIGN first attempt)
- Approaches tried: 8 (S1 OBSERVE feasibility; S2 ACT-A scaffold;
  S3 ACT-B prep `singularHomologyFunctor` API verification;
  S4 ACT-C prep prism-operator construction blueprint;
  S5 ACT-B exec — thin local axiom + substantive ball-homology theorem;
  S6 OBSERVE — sphere-side ACT-D scoping via Mathlib API survey;
  S7 ACT-D-1 exec — thin B2 surrogate axiom + substantive sphere theorem;
  S8 ACT-D-2 DESIGN — G7 algebraic bridge specification, doc-only)

## Historical Sessions (S6 OBSERVE summary, retained verbatim)

S6 OBSERVE — doc-only Mathlib API survey of sphere-side
infrastructure at the pinned rev (`v4.26.0`,
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) to scope the ACT-D
execution sequence. Output: knowledge.md Section L (sub-sections
L1–L9), no Lean changes. Key deliverables: L1 TopCat sphere API
discovery (`TopCat.disk`/`diskBoundary`/`sphere`/`ball`), L3 B2
gap classification refinement (B2-CW path), L4 exact thin
B2-surrogate axiom signature, L5 exact substantive sphere theorem
signature, L7 S7–S10 execution plan, L8 build-risk analysis for
S7 ACT-D-1 (lower than S5).
