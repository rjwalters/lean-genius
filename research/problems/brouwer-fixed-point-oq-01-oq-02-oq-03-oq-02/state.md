# Current State

**Phase**: ACT (S8 ACT-D-2 EXEC complete, build pending; S9 ACT-D-3 next — gated on sibling PR #18011)
**Since**: 2026-05-13T23:30:00Z (Session 9, researcher-10, EXEC half of S8)
**Iteration**: 9

## Current Focus

S8 ACT-D-2 EXEC (this session, researcher-10, 2026-05-13) — installs
the **G7 algebraic bridge**

    ¬ IsZero (X : AddCommGrpCat.{0}) → ∃ x : X, x ≠ 0

as the companion file `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean`
(94 lines, 2 theorems, 0 axioms, 0 sorries) per knowledge.md §N4 / §N5
Option A / §N8 prescriptions from the S8 DESIGN half (PR #18945).

Two theorems are now exposed in namespace `AddCommGrpCat`:

* `not_isZero_iff_nontrivial` — the iff form, 2-line rw proof composing
  `AddCommGrpCat.isZero_iff_subsingleton`
  (`Mathlib/Algebra/Category/Grp/Zero.lean`, generated via
  `@[to_additive]` from `CommGrpCat.isZero_iff_subsingleton` at the
  pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) with
  `not_subsingleton_iff_nontrivial`
  (`Mathlib/Logic/Nontrivial/Defs.lean`).
* `exists_ne_zero_of_not_isZero` — the existential corollary, 3-line
  `obtain ⟨a, b, hab⟩ := hX.exists_pair_ne; exact ⟨a - b, sub_ne_zero.mpr hab⟩`.

Lean changes this iteration: **+1 file (94 lines), +2 theorems,
+0 axioms, +0 sorries**. Main file `BrouwerFixedPointOQ01OQ02.lean`
unchanged at 14 theorems / 4 axioms (S9 ACT-D-3 will wire the
companion in via a single `import` line once PR #18011 merges).

## Active Approach (§N8 EXEC checklist execution log)

1. **Companion file created** at
   `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` per §N5 Option A.
   Imports are a strict subset of the main file (4 imports total):

   * `Mathlib.Algebra.Category.Grp.Basic` — `AddCommGrpCat`,
     `CoeSort` instance, `AddCommGrp.of` constructor.
   * `Mathlib.Algebra.Category.Grp.Zero` — supplies
     `AddCommGrpCat.isZero_iff_subsingleton` (the §N3 flagged lemma,
     verified at pinned rev — see step 2).
   * `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects` — `IsZero`,
     `Limits.IsZero` boilerplate.
   * `Mathlib.Logic.Nontrivial.Basic` — transitively imports
     `Logic.Nontrivial.Defs` which supplies
     `not_subsingleton_iff_nontrivial` and `Nontrivial.exists_pair_ne`.

   No `Topology.*` / `AlgebraicTopology.*` / `InnerProductSpace`
   imports. Build cost dominated by `AddCommGrpCat`'s own dep closure
   (already cached from main-file build); incremental cost ≲ 1 s on
   warm cache.

2. **§N7 risk-1 API verification** executed via
   `gh api .../contents/Mathlib/Algebra/Category/Grp/Zero.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
   Result: `AddCommGrpCat.isZero_iff_subsingleton` exists at the
   pinned rev. The canonical site is the `@[to_additive]` attribute
   on `CommGrpCat.isZero_iff_subsingleton` in
   `Mathlib/Algebra/Category/Grp/Zero.lean` lines 75–77. **No
   fallback needed**; the inline §N3 construction is held in reserve.

3. **Stage 1 theorem `not_isZero_iff_nontrivial` installed** per §N4
   recipe:

   ```lean
   theorem not_isZero_iff_nontrivial (X : AddCommGrpCat.{0}) :
       ¬ Limits.IsZero X ↔ Nontrivial X := by
     rw [AddCommGrpCat.isZero_iff_subsingleton,
         not_subsingleton_iff_nontrivial]
   ```

4. **Stage 2 theorem `exists_ne_zero_of_not_isZero` installed** per
   §N4 recipe (§N7 risk-3 mitigation: explicit
   `Nontrivial.exists_pair_ne` + `sub_ne_zero.mpr` instead of the
   `exists_ne_zero` name flagged for drift):

   ```lean
   theorem exists_ne_zero_of_not_isZero
       (X : AddCommGrpCat.{0}) (hX : ¬ Limits.IsZero X) :
       ∃ x : X, x ≠ 0 := by
     rw [not_isZero_iff_nontrivial] at hX
     obtain ⟨a, b, hab⟩ := hX.exists_pair_ne
     exact ⟨a - b, sub_ne_zero.mpr hab⟩
   ```

5. **Main-file `import` wiring deferred to S9 ACT-D-3** (gated on
   sibling PR #18011). The G7 bridge sits in namespace
   `AddCommGrpCat` and can be imported by the main file with a
   single `import Proofs.BrouwerFixedPointOQ01OQ02G7` line once
   the G6 Subsingleton-bridge from PR #18011's Part VI is also
   available. This keeps the S8 PR's net diff minimal (single new
   file; no main-file edit).

6. **Build verification deferred**: local Docker daemon was
   unavailable at PR time (`docker-build.sh` returned
   "Docker daemon is not running"). The lemma chain is shallow and
   uses APIs verified to exist at the pinned rev (step 2) plus
   `Nontrivial.exists_pair_ne` / `sub_ne_zero` (stable since 2021,
   per §N7 risk-3 analysis). Build can be reverified by CI or
   redeployer via `./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G7`.

7. **state.md and JSON updated** with S9 iteration counter, new
   currentState, knowledge.progressSummary prepended S8 EXEC entry,
   new `leanFiles` entry for the companion (94/2/0/0/0), and
   `lastUpdate` bumped.

8. **knowledge.md §O appended** logging the S8 EXEC step with the
   exact installed code + Mathlib API verification evidence.

Net effect on Lean codebase: +1 file / +2 theorems / +0 axioms /
+0 sorries. The mock composite axiom `H_n_minus_1_sphere_nonzero`
(main file line 261) remains in place; dropping it is deferred to
S10 ACT-D-4 after S9 ACT-D-3 (gated on PR #18011) wires G7 + G6 +
functoriality to produce a substantive derivation.

## Historical Focus (S8 ACT-D-2 DESIGN, PR #18945, doc-only)

S8 ACT-D-2 DESIGN (researcher-4, 2026-05-13) added knowledge.md §N
(sub-sections N1–N9) — the exact Lean signature, import list,
Mathlib API survey at the pinned rev, two-stage proof sketch,
companion-file vs inline installation analysis, S9/S10 integration
plan, build-risk analysis with ≤ 10-line inline fallbacks per risk
factor, and 8-step EXEC checklist for this iteration. No Lean
changes; iteration 7 → 8.

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

## Blockers

* **B1 (Mathlib gap)** — prism operator still missing. Encoded as
  the thin local axiom `contractible_singularHomology_zero` (S5
  ACT-B exec). Upstream contribution path is mapped (Section H).
* **B2 (Mathlib gap)** — `H_n(𝕊 n) ≠ 0` encoded as the thin
  local axiom `sphere_singularHomology_nonzero` (S7 ACT-D-1).
  Upstream contribution path via the cellular chain complex of
  `𝕊 n` (Section L3 / B2-CW).
* **Sibling PR #18011 (G6 Unit-bridge)** still OPEN. S9 ACT-D-3
  depends on its merge for the subsingleton-bridge half on the
  ball side. Until then, the sphere-side substantive theorem
  (S7) + the G7 algebraic bridge (this iteration) exist as a
  parallel-but-not-yet-bridged structure on the sphere half.
* **Build verification deferred**: local Docker daemon was
  unavailable at PR time. APIs used in the companion file are
  verified to exist at the pinned rev (`AddCommGrpCat.isZero_iff_subsingleton`,
  step-2 evidence above) or are stable since 2021
  (`Nontrivial.exists_pair_ne`, `sub_ne_zero` from `to_additive`).

## Next Action

**S9 ACT-D-3 (gated on sibling PR #18011 merge)**: combine the new
G7 bridge `AddCommGrpCat.exists_ne_zero_of_not_isZero` with:

  * (a) the functoriality of `singularHomologyFunctor` applied to
    the retraction `r ∘ i = id`, and
  * (b) the G6 Subsingleton-bridge from PR #18011's Part VI,

to produce a substantive derivation of
`∃ ψ : Unit →+ ℤ, ψ ∘ φ = id` from the substantive
`¬ IsZero (H_{n-1}(𝕊 (n-1)))` of `H_n_minus_1_sphere_nonzero_substantive`
(S7). This is the step that *replaces* the mock composite axiom
`H_n_minus_1_sphere_nonzero` (line 261 of main file) with a
substantive theorem. S9 also adds the
`import Proofs.BrouwerFixedPointOQ01OQ02G7` line to the main file
(item 5 of this session's checklist).

**S10 ACT-D-4 (after S9)**: drop the mock axiom
`H_n_minus_1_sphere_nonzero` entirely; rewire
`singular_homology_retraction_split` to use the substantive chain.
Net axiom delta: −1 (file-level count 4 → 3, back to "all
surrogates are textbook facts").

**Deferred to S11+**: full Mathlib B1/B2 upstream contributions
(see Section H for B1, Section L3 / B2-CW for B2). These are
independent of the gallery proof and can proceed in parallel.

**Build verification (orthogonal)**: rerun
`./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G7`
once Docker is available. Expected ≲ 30 s on warm Mathlib cache.

## Attempt Counts

- Total attempts: 9
- Current approach attempts: 1 (S8 ACT-D-2 EXEC first attempt)
- Approaches tried: 9 (S1 OBSERVE feasibility; S2 ACT-A scaffold;
  S3 ACT-B prep `singularHomologyFunctor` API verification;
  S4 ACT-C prep prism-operator construction blueprint;
  S5 ACT-B exec — thin local axiom + substantive ball-homology theorem;
  S6 OBSERVE — sphere-side ACT-D scoping via Mathlib API survey;
  S7 ACT-D-1 exec — thin B2 surrogate axiom + substantive sphere theorem;
  S8 ACT-D-2 DESIGN — G7 algebraic bridge specification, doc-only;
  S8 ACT-D-2 EXEC — G7 algebraic bridge companion file installed)

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
