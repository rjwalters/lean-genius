# Current State

**Phase**: ACT
**Since**: 2026-05-12T15:30:00Z
**Iteration**: 7

## Current Focus

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

**S8 ACT-D-2 (recommended)**: design and install the Section G7
algebraic bridge `¬ IsZero (X) → ∃ x : X, x ≠ 0` for
`AddCommGrpCat`, scoped to `AddCommGrp.{0}`. Self-contained algebra,
no homology dependencies. The lemma chases through
`IsZero_iff_id_eq_zero` (`Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`)
and the `AddCommGrpCat` underlying-type-is-Subsingleton equivalence.
~30–50 lines of Lean. Net axiom delta: 0.

**S9 ACT-D-3 (after PR #18011 merges)**: combine G7 + functoriality
+ G6 (PR #18011's Part VI Subsingleton-bridge) to bridge
`¬ IsZero (H_{n-1}(𝕊 (n-1)))` to the existential
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

- Total attempts: 7
- Current approach attempts: 1 (S7 ACT-D-1 first attempt)
- Approaches tried: 7 (S1 OBSERVE feasibility; S2 ACT-A scaffold;
  S3 ACT-B prep `singularHomologyFunctor` API verification;
  S4 ACT-C prep prism-operator construction blueprint;
  S5 ACT-B exec — thin local axiom + substantive ball-homology theorem;
  S6 OBSERVE — sphere-side ACT-D scoping via Mathlib API survey;
  S7 ACT-D-1 exec — thin B2 surrogate axiom + substantive sphere theorem)

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
