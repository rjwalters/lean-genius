# Research State: euler-identity-oq-01-oq-04

## Current State
**Phase**: ACT (Iter 2 ACT-1 — Path A wrapper scaffold SHIPPED with three named sorries; build-verification + sorry-discharge pending Iter 3 ACT-2)
**Path**: full
**Since**: 2026-04-05T19:03:34-07:00 (initial selection; first substantive iteration 2026-06-01; first Lean edit 2026-06-03)
**Last Updated**: 2026-06-03 (Iter 2 ACT-1 — scaffold shipped; iteration 2→3; +1 Lean file (~125 LOC, 0 axioms, 3 sorries), researcher-1)
**Iteration**: 3

## Iter 2 ACT-1 (2026-06-03, researcher-1) — Path A wrapper scaffold shipped

First Lean edit on this slug. Ships `proofs/Proofs/EulerIdentityOQ01OQ04.lean` (~125 LOC) implementing the paste-ready Path A skeleton from the 2026-06-01 Iter 1 ORIENT/PREP session log. The file is **scaffold-only**: three named sorries (`left_inv`, `right_inv`, `map_add'`) inside the `AddEquiv` record, each annotated with the Mathlib lemma it should chain through. No build verification this iteration (host Docker image missing + corrupted blob; build deferred to Iter 3 ACT-2 next researcher).

- **Definition shipped**: `addCircleEquivAdditiveCircle : AddCircle (2 * π) ≃+ Additive Circle` with `toFun x := Additive.ofMul (AddCircle.toCircle x)` and `invFun y := AddCircle.homeomorphCircle'.symm (Additive.toMul y)`. The forward map is `AddCircle.toCircle`; the inverse is the `symm` of Mathlib's `homeomorphCircle'`.
- **API lemmas shipped (both `@[simp]`, both `rfl`-provable)**: `addCircleEquivAdditiveCircle_apply` and `addCircleEquivAdditiveCircle_symm_apply`. These should compile out-of-the-box; they document the forward and inverse maps as `Additive.ofMul ∘ AddCircle.toCircle` and `AddCircle.homeomorphCircle'.symm ∘ Additive.toMul` respectively.
- **Three sorries with discharge strategies**: each labeled in file comments with the Mathlib lemma it should chain through (`homeomorphCircle'.left_inv`, `homeomorphCircle'.right_inv`, `AddCircle.toCircle_add` + `Additive.ofMul_mul`). Expected discharge cost: 3-8 lines total across the three sorries.
- **Build verification deferred**: local Docker image `lean4-arm64:v4.26.0` missing + host has a corrupted blob; rebuilding would dominate iteration budget. The `proofs/.lake` symlink in the worktree is self-referential, so direct `lake build` is also not wired (and CLAUDE.md blocks it). Build verification + tactic polish moves to Iter 3 ACT-2.
- **File state**: `proofs/Proofs/EulerIdentityOQ01OQ04.lean` (~125 LOC, 0 axioms, 3 sorries), `proofs/Proofs/EulerIdentityOQ01OQ01OQ01.lean` and the other three sibling files unchanged. No gallery-side (`src/data/proofs/euler-identity-*/`) edits; those are downstream of a sorry-clean build.
- **No edits to** `problem.md` or `knowledge.md` (still the template-placeholder state flagged by Iter 1 PREP). Documentation pass deferred.

Session log: `sessions/2026-06-03-iter2-act1-pathA-scaffold-shipped.md`.

## Iter 1 ORIENT/PREP (2026-06-01, researcher-1) — Mathlib bearer audit + paste-ready wrapper sketch

First substantive iteration on this slug after 57 idle days. Doc-only PREP advancing the slug from initial OBSERVE (Iter 1) to DECIDE (Iter 2 ready). Maps the v4.26.0 Mathlib API at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, reads the four sibling Euler-identity Lean files, and recommends an ACT direction.

- **Selection-report bearer drift detected**: `Complex.expMapCircle` was REFACTORED to `Circle.exp` (`Mathlib/Analysis/Complex/Circle.lean:108`, a `C(ℝ, Circle)` continuous map, NOT a `MonoidHom`). The additive-group-hom upgrade exists as `Circle.expHom : ℝ →+ Additive Circle` (line 131). Other selection-report APIs (`Complex.exp_periodic`, `AddCircle`, `AddCircle.homeomorphCircle`, `QuotientAddGroup.quotientKerEquivRange`, `MonoidHom.ker`) all unchanged and reachable.
- **Decisive Mathlib bearer**: `AddCircle.homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle` at `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean:168` — **a `≃ₜ` (Homeomorph), NOT a `≃+` (AddEquiv)**. So Mathlib gives the topological bijection but stops short of packaging the group isomorphism that OQ-04 asks for.
- **Additive structure available separately** in same file: `AddCircle.toCircle_add` (line 144), `AddCircle.toCircle_zero` (line 152), `AddCircle.injective_toCircle` (line 158). `PontryaginDuality.lean:47` already constructs the additive-monoid-hom structure inline (`AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩`) — i.e., the AddMonoidHom is constructible from existing lemmas but is **not exposed as a named definition**.
- **Sibling file `EulerIdentityOQ01OQ01OQ01.lean` already proves all sub-lemmas** (241 LOC, 0 axioms, 0 sorries): `circleMap_add` (hom), `norm_circleMap` (image on S¹), `circleHom : Multiplicative ℝ →* ℂˣ` (packaged group hom), `continuous_circleMap`, `circleMap_eq_one_iff` (kernel = 2π·ℤ), `circleMap_surjective_unit_circle`. The sibling's §8 docstring explicitly says "kernel is 2π·ℤ (so S¹ ≅ ℝ/2πℤ)" but **stops short of constructing the actual `AddEquiv`/`MulEquiv`**.
- **Two ACT paths sketched**:
  - **Path A (recommended)**: wrap Mathlib's `homeomorphCircle'` as `addCircleEquivAdditiveCircle : AddCircle (2 * π) ≃+ Additive Circle` (~15-25 LOC). Three sorries discharged via `simp` over existing left_inv/right_inv + `toCircle_add`. Paste-ready skeleton in session log §"Path A".
  - **Path B (alternative)**: First isomorphism theorem applied to the sibling's `circleHom` (~40-60 LOC). Requires range-restriction + AddSubgroup-vs-AddCircle bridge plumbing. De-recommended for cost reasons.
- **Outstanding question for gallery owner**: ≃+ packaging (Path A default) vs ≃* packaging (Path B style)? Path A recommended.

**File state at PREP time**: All four `EulerIdentity*.lean` files unchanged. `EulerIdentityOQ01OQ01OQ01.lean` 241 LOC, 0 axioms, 0 sorries (the sibling that already does the heavy lifting). No new sorries/axioms introduced by this PREP.

**No edits outside this PREP's three files**: this session log + this `state.md` block + research JSON `currentState` refresh. **NO edits to `problem.md`** (still the unfilled generic template — flagged for a future documentation pass; this PREP + selection-report + state.md carry the authoritative context for now) or `knowledge.md`. No Lean file edits. No gallery `meta.json` edits. Session log: `sessions/2026-06-01-iter1-orient-prep-mathlib-bearer-audit.md`.

## Current Focus

**Iteration 3 (Iter 2 ACT-1, this iter, researcher-1, 2026-06-03)**: First Lean edit on the slug. Ships the Path A wrapper scaffold (~125 LOC including ~65 LOC of docstring/strategy comments) per the 2026-06-01 PREP's paste-ready skeleton. Three named sorries inside the `AddEquiv` record; two `@[simp]` API lemmas (`apply`/`symm_apply`) which are `rfl`-provable. Build verification deferred — host Docker image missing + corrupted blob.

**Highest-readiness next ACT — Iter 3 ACT-2 (next researcher)**: Run `./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04`, then discharge the three sorries per the per-sorry strategy table in the 2026-06-03 session log. Expected discharge: 3-8 lines total across the three sorries; 5-15 min of tactic polish.

## Active Approach

**Path A (recommended)**: Wrap `AddCircle.homeomorphCircle'` as `AddCircle (2 * π) ≃+ Additive Circle`. Defaults to ≃+ packaging (matches Mathlib's `Circle.expHom : ℝ →+ Additive Circle` convention).

**Path B (alternative, de-recommended)**: First isomorphism theorem on sibling's `circleHom : Multiplicative ℝ →* ℂˣ`. Documented as an educational follow-up if gallery owner wants the abstract-quotient-theorem connection.

## Attempt Count

- Total attempts: 1 (Iter 2 ACT-1 scaffold ship 2026-06-03)
- Current approach attempts: 1 (Path A scaffold-only ship)
- Approaches tried: 1 (Path A; Path B still de-recommended, available as alternate follow-up)

## Blockers

None on the math side. The ACT-2 sorry discharge is a 5-15 min tactic-polish job per the per-sorry strategy table in the 2026-06-03 session log.

**Soft transient blocker**: host Docker environment (image missing + corrupted blob) at this researcher's worktree was unable to build-verify the scaffold this iteration. Iter 3 ACT-2 should restore Docker access (image rebuild or operator intervention) before running `./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04`.

## Next Action

Iter 3 ACT-2 (next researcher): (1) Restore Docker / run `./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04`; (2) discharge the three sorries in the `addCircleEquivAdditiveCircle` `AddEquiv` record per the per-sorry strategy table in `sessions/2026-06-03-iter2-act1-pathA-scaffold-shipped.md`; (3) update this `state.md` + the registry JSON's `leanFiles[]` entry for the new file once the build is clean.
