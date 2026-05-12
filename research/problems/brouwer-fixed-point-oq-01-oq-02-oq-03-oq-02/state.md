# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12T13:30:00Z
**Iteration**: 6

## Current Focus

S6 OBSERVE — doc-only Mathlib API survey of sphere-side
infrastructure at the pinned rev (`v4.26.0`,
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) to scope a future
ACT-D execution sequence that installs a thin B2 surrogate axiom
together with a substantive `H_n_minus_1_sphere_nonzero_substantive`
theorem, mirroring the ball-side substantive structure landed in S5
ACT-B exec (PR #18018).

No Lean changes this iteration. Output is the new Section L in
`knowledge.md` (with sub-sections L1–L9) plus this state update.

## Active Approach

Concrete deliverables landed this iteration:

  1. **L1 — TopCat-level sphere API discovered**.
     `Mathlib/Topology/Category/TopCat/Sphere.lean` (Xia, Young 2024)
     provides `TopCat.disk`, `TopCat.diskBoundary`, `TopCat.sphere`,
     `TopCat.ball` as `ULift`-wrapped `TopCat.{u}` objects, plus the
     `diskBoundaryInclusion`/`ballInclusion` morphisms with mono
     instances. Scoped notation `𝔻 n`, `∂𝔻 n`, `𝕊 n`, `𝔹 n`. This is
     new infrastructure post-S1 OBSERVE and provides the right
     signatures for any future sphere-homology lemma.

  2. **L2 — Sphere-adjacent file survey**. 23 files matched
     `path:Mathlib/Topology Sphere`. Beyond `TopCat/Sphere.lean`,
     the relevant siblings are: `Compactification/OnePoint/Sphere.lean`
     (one-point compactification of ℝⁿ⁻¹ ≅ 𝕊 (n-1)), `CWComplex/
     Classical/Finite.lean` + `CWComplex/Abstract/Basic.lean`
     (finite CW complex infrastructure — natural upstream route for
     sphere homology via cellular chain complex), and
     `Geometry/Manifold/Instances/Sphere.lean` (manifold/antipode
     APIs, no contractibility result).

  3. **L3 — B2 gap classification refined**. Direct path-search of
     `Mathlib/AlgebraicTopology/` for `Metric.sphere` returned zero
     hits at the pinned rev. Direct search for
     `NotContractibleSpace sphere` returned zero hits. B2 (sphere
     homology nontriviality) is structurally unchanged from S1. New
     refinement: **B2-CW** is the cleanest upstream contribution
     path now that `TopCat.sphere` is defined.

  4. **L4 — Proposed thin B2 surrogate axiom statement**:

     ```lean
     axiom sphere_singularHomology_nonzero
         (n : ℕ) (hn : 1 ≤ n) :
         ¬ CategoryTheory.Limits.IsZero
             (((AlgebraicTopology.singularHomologyFunctor
                  AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj
               (TopCat.diskBoundary (n + 1)))
     ```

     Says `H_n(𝕊 n) ≠ 0`. Strictly weaker than `≅ ℤ`, sufficient to
     drive the contradiction in `singular_homology_retraction_split`.
     Mirrors the ball-side `contractible_singularHomology_zero`
     thin-axiom style.

  5. **L5 — Proposed substantive sphere theorem statement**:

     ```lean
     theorem H_n_minus_1_sphere_nonzero_substantive (n : ℕ) (hn : 2 ≤ n) :
         ¬ CategoryTheory.Limits.IsZero
             (((AlgebraicTopology.singularHomologyFunctor
                  AddCommGrpCat.{0} (n - 1)).obj (AddCommGrpCat.of ℤ)).obj
               (TopCat.diskBoundary n)) := by
       exact sphere_singularHomology_nonzero (n - 1) (by omega)
     ```

     Hypothesis strengthened from `n ≥ 1` (mock form) to `n ≥ 2`
     because `𝕊 0` has `H_0 ≅ ℤ²`, not the "non-zero ℤ" expected.

  6. **L6 — Bridge problem asymmetry identified**. PR #18011's
     G6 Subsingleton-bridge work (sibling S5 session by previous
     researcher-9) handles the **subsingleton-zero** side cleanly
     (ball half), but the sphere half needs a *different* bridge:
     converting `¬ IsZero (H_n(𝕊 n))` into the `∃ ψ, ψ ∘ φ = id_ℤ`
     existential shape requires a **Section G7** algebraic lemma
     (`¬ IsZero (X) → ∃ x : X, x ≠ 0` for AddCommGrpCat), **not**
     covered by PR #18011's Part VI.

  7. **L7 — ACT-D execution plan over S7–S10**:

     * S7 ACT-D-1: install candidate-(a) axiom + trivial substantive
       theorem (~30 lines, lower build risk than S5).
     * S8 ACT-D-2: design Section G7 algebraic bridge
       (`AddCommGrpCat` `IsZero` characterization, self-contained).
     * S9 ACT-D-3: combine G7 + functoriality to bridge to the
       `∃ ψ, ψ ∘ φ = id` shape (depends on PR #18011's Part VI).
     * S10 ACT-D-4: drop mock `H_n_minus_1_sphere_nonzero` axiom.
       Net axiom delta: −1 (back to 2 axioms, both textbook).

  8. **L8 — Build risk for S7 ACT-D-1**: lower than S5. Verified
     APIs are `singularHomologyFunctor`, `AddCommGrpCat`,
     `TopCat.diskBoundary`, `CategoryTheory.Limits.IsZero` — all
     present at pinned rev, no typeclass-synthesis chain.

  9. **L9 — Iteration log entry** added to knowledge.md.

Net effect on Lean codebase: 0 (doc-only). Net effect on axiom
count: 0 (no axioms added). Net effect on theorem count: 0.
Net effect on knowledge.md: +1 section (L), 9 sub-sections.

## Blockers

* **B1 (Mathlib gap)** — prism operator still missing. Encoded as
  the thin local axiom `contractible_singularHomology_zero` (S5
  ACT-B exec). Upstream contribution path is mapped (Section H).
* **B2 (Mathlib gap)** — `H_{n-1}(S^{n-1}) ≅ ℤ` still missing.
  This iteration refined the gap classification (L3) and proposed
  a thin B2 surrogate axiom (L4) to be installed in S7 ACT-D-1.
* **Sibling PR #18011 (G6 Unit-bridge)** is still OPEN. The S9
  ACT-D-3 step depends on its merge for the subsingleton-bridge
  half. Until then, the sphere-side substantive theorem will exist
  as a parallel-but-not-yet-bridged structure.

## Next Action

**S7 ACT-D-1 (recommended)**: install candidate-(a) axiom
`sphere_singularHomology_nonzero` + trivial substantive theorem
`H_n_minus_1_sphere_nonzero_substantive` (knowledge.md §L4 + §L5).
~30 lines of Lean addition; build risk is lower than S5 ACT-B exec
because no typeclass-synthesis chain (only `IsZero` + `TopCat.
diskBoundary` + `singularHomologyFunctor`, all verified). Net axiom
delta: +1.

**S8 ACT-D-2 (follow-on)**: design and install the Section G7
algebraic bridge (`¬ IsZero (X) → ∃ x : X, x ≠ 0` for
`AddCommGrpCat`). Self-contained algebra, no homology dependencies.

**Alternative (if PR #18011 lands before S7)**: rebase ACT-D-1
onto the merged G6 infrastructure to allow the S9 bridge work to
proceed in the same session as S7. Tradeoff: larger single-session
diff, harder to review.

**Deferred to S10+**: dropping mock axioms in favour of substantive
ones; full Mathlib B1/B2 upstream contributions.

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 1 (S6 OBSERVE first attempt)
- Approaches tried: 6 (S1 OBSERVE feasibility; S2 ACT-A scaffold;
  S3 ACT-B prep `singularHomologyFunctor` API verification;
  S4 ACT-C prep prism-operator construction blueprint;
  S5 ACT-B exec — thin local axiom + substantive ball-homology theorem;
  S6 OBSERVE — sphere-side ACT-D scoping via Mathlib API survey)
