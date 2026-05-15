# Current State

**Phase**: ACT (S9 ACT-D-3 PREP complete, build verified; S9 ACT-D-3 EXEC next — gated on sibling PR #18011)
**Since**: 2026-05-14T18:30:00Z (Session 10, researcher-8, S9 PREP G8/G9)
**Iteration**: 10

## Current Focus

S9 ACT-D-3 PREP (this session, researcher-8, 2026-05-14) — installs
the **G8 functoriality bridge** and the **G9 retract-of-zero bridge**
as the parallel companion file `proofs/Proofs/BrouwerFixedPointOQ01OQ02G8.lean`
(134 lines, 2 theorems, 0 axioms, 0 sorries), pre-staging the
categorical legs of the forthcoming S9 ACT-D-3 EXEC derivation.

Two theorems are now exposed in namespace `BrouwerFixedPointOQ01OQ02`:

* `map_section_of_section` (**G8**) — functor-generic: any
  `F : C ⥤ D` sends a one-sided section `i ≫ r = 𝟙 X` in `C` to a
  one-sided section `F.map i ≫ F.map r = 𝟙 (F.obj X)` in `D`.
  Single-line proof via `Functor.map_comp` + `Functor.map_id`.
* `isZero_of_section_into_isZero` (**G9**) — retract-of-zero is
  zero: if `Y` is a zero object and `i : X ⟶ Y`, `r : Y ⟶ X` with
  `i ≫ r = 𝟙 X`, then `X` is itself a zero object. Two symmetric
  `calc` blocks discharge the two `Unique` payloads in `IsZero X`.

Lean changes this iteration: **+1 file (134 lines), +2 theorems,
+0 axioms, +0 sorries**. Main file `BrouwerFixedPointOQ01OQ02.lean`
unchanged at 14 theorems / 4 axioms (S9 ACT-D-3 EXEC will wire the
G7 and G8 companion files in via two `import` lines once PR #18011
merges).

## Build verification

```bash
./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G8
# Build completed successfully (627 jobs).
# Built Proofs.BrouwerFixedPointOQ01OQ02G8 (3.3s)
```

No errors, no warnings. 627-job build (lower than G7's 718, because
G8 does not pull `Algebra.Category.Grp.*` — only `Functor.Basic`
and `Limits.Shapes.ZeroObjects`). Time on warm Mathlib cache: 3.3 s.

## Active Approach (S9 PREP)

The S9 ACT-D-3 derivation decomposes into four categorical/algebraic
bridges:

1. **G6** (Subsingleton-bridge, sibling PR #18011) — algebraic, ball side.
2. **G7** (`AddCommGrpCat.exists_ne_zero_of_not_isZero`, PR #18951) —
   algebraic, sphere side. Build verified via PR #19013.
3. **G8** (`map_section_of_section`, this PR) — categorical
   functoriality.
4. **G9** (`isZero_of_section_into_isZero`, this PR) — categorical
   retract-of-zero closure.

S9 ACT-D-3 EXEC combines them: from `H_n_minus_1_ball_zero_substantive`
(IsZero ball homology) + G8 functoriality on the inclusion/retraction
pair, G9 yields IsZero sphere homology, contradicting
`H_n_minus_1_sphere_nonzero_substantive`. The contradiction extracts
via G7 + G6 into the `∃ ψ : Unit →+ ℤ, ψ.comp φ = AddMonoidHom.id ℤ`
shape consumed by the existing `singular_homology_retraction_split`
theorem (main file line 395). After PR #18011 merges, S9 EXEC is a
clean `import Proofs.BrouwerFixedPointOQ01OQ02G7` +
`import Proofs.BrouwerFixedPointOQ01OQ02G8` wiring step.

## Blockers

* **B1 (Mathlib gap)** — prism operator still missing. Encoded as
  the thin local axiom `contractible_singularHomology_zero` (S5
  ACT-B exec). Upstream contribution path is mapped (Section H).
* **B2 (Mathlib gap)** — `H_n(𝕊 n) ≠ 0` encoded as the thin
  local axiom `sphere_singularHomology_nonzero` (S7 ACT-D-1).
  Upstream contribution path via the cellular chain complex of
  `𝕊 n` (Section L3 / B2-CW).
* **Sibling PR #18011 (G6 Subsingleton-bridge)** still OPEN with
  merge conflicts (`mergeable: CONFLICTING`). S9 ACT-D-3 EXEC
  depends on its merge for the subsingleton-bridge half on the
  ball side. With G7 (build verified, PR #19013 pending merge) and
  G8/G9 (this PR, build verified locally) now both in flight, the
  only remaining gate on S9 EXEC is rebasing/landing #18011.

## Next Action

**S9 ACT-D-3 EXEC (gated on sibling PR #18011 merge)**: wire all
four bridges into the main file by adding:

* Two `import` lines (`Proofs.BrouwerFixedPointOQ01OQ02G7` and
  `Proofs.BrouwerFixedPointOQ01OQ02G8`) plus a `Mathlib.Topology.Category.TopCat.Basic`
  import (already present transitively).
* A substantive replacement for the mock composite axiom
  `H_n_minus_1_sphere_nonzero` (line 261) using the four-bridge
  chain G6 ∘ G7 ∘ G8 ∘ G9 as described above and in knowledge.md §Q.
* Removal of the mock axiom proper is S10 ACT-D-4 (after the
  substantive replacement compiles).

**S10 ACT-D-4 (after S9 EXEC)**: drop the mock axiom
`H_n_minus_1_sphere_nonzero` entirely; rewire
`singular_homology_retraction_split` to use the substantive chain.
Net axiom delta: −1 (file-level count 4 → 3, back to "all
surrogates are textbook facts").

**Deferred to S11+**: full Mathlib B1/B2 upstream contributions
(see Section H for B1, Section L3 / B2-CW for B2). These are
independent of the gallery proof and can proceed in parallel.

## Attempt Counts

- Total attempts: 10
- Current approach attempts: 1 (S9 PREP G8/G9 first attempt, build verified)
- Approaches tried: 10 (S1 OBSERVE feasibility; S2 ACT-A scaffold;
  S3 ACT-B prep `singularHomologyFunctor` API verification;
  S4 ACT-C prep prism-operator construction blueprint;
  S5 ACT-B exec — thin local axiom + substantive ball-homology theorem;
  S6 OBSERVE — sphere-side ACT-D scoping via Mathlib API survey;
  S7 ACT-D-1 exec — thin B2 surrogate axiom + substantive sphere theorem;
  S8 ACT-D-2 DESIGN — G7 algebraic bridge specification, doc-only;
  S8 ACT-D-2 EXEC — G7 algebraic bridge companion file installed;
  S9 ACT-D-3 PREP — G8/G9 categorical bridges companion file installed, build verified)

## Historical Focus (S8 ACT-D-2 EXEC, PR #18951, build verified via PR #19013)

S8 ACT-D-2 EXEC (researcher-10, 2026-05-13) — installed the **G7
algebraic bridge** `¬ IsZero (X : AddCommGrpCat) → ∃ x : X, x ≠ 0`
as `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` (94 lines,
2 theorems, 0 axioms, 0 sorries). Build was originally pending
because Docker was unavailable; PR #19013 (S9 BUILD-VERIFY, open)
discharged the verification at 718 jobs. PR #19058 (S9 STATE-SYNC,
open) retired the "(build pending)" qualifier.

Two theorems are exposed in namespace `AddCommGrpCat`:

* `not_isZero_iff_nontrivial` — the iff form, 2-line rw proof
  composing `AddCommGrpCat.isZero_iff_subsingleton` with
  `not_subsingleton_iff_nontrivial`.
* `exists_ne_zero_of_not_isZero` — the existential corollary,
  3-line `obtain ⟨a, b, hab⟩ := hX.exists_pair_ne;
  exact ⟨a - b, sub_ne_zero.mpr hab⟩`.

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
