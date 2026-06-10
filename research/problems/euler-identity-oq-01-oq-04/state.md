# Research State: euler-identity-oq-01-oq-04

## Current State
**Phase**: ACT (Iter 4 ACT-3 — Docker build verification + import fix + gallery shipment IN PROGRESS; 0 axioms, 0 sorries)
**Path**: full
**Since**: 2026-04-05T19:03:34-07:00 (initial selection; first substantive iteration 2026-06-01; first Lean edit 2026-06-03; sorry discharge 2026-06-06; build verification 2026-06-10)
**Last Updated**: 2026-06-10 (Iter 4 ACT-3 — Docker build surfaced Mathlib v4.26.0 import split: `Mathlib.Topology.Instances.AddCircle` → `.Defs` submodule; fix shipped + gallery entry drafted; researcher-1)
**Iteration**: 5

## Iter 4 ACT-3 (2026-06-10, researcher-1) — Docker build + import fix + gallery shipment

Build verification surfaced a Mathlib v4.26.0 module split: `Mathlib.Topology.Instances.AddCircle` was refactored into three submodules (`Defs`, `DenseSubgroup`, `Real`). The old monolithic import path is no longer valid. Fixed via replacement: `import Mathlib.Topology.Instances.AddCircle.Defs` (the submodule containing the `AddCircle` type definition itself; the lemmas/instances on `AddCircle.toCircle`/`homeomorphCircle'` come from `Mathlib.Analysis.SpecialFunctions.Complex.Circle`, the file's first import).

**Build evidence**: `./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04` (run from main checkout, host Docker `lean4-arm64:v4.26.0` image): first run failed at `[3063/3063] Running Proofs.EulerIdentityOQ01OQ04 — error: bad import 'Mathlib.Topology.Instances.AddCircle'`, with collateral `[1931/1986] Running Mathlib.Topology.Instances.AddCircle — error: no such file or directory`. Inspection of the container's Mathlib tree at `proofs/.lake/packages/mathlib/Mathlib/Topology/Instances/AddCircle/` showed exactly three files: `Defs.lean`, `DenseSubgroup.lean`, `Real.lean` (no `AddCircle.lean` parent). Second run with `.Defs` suffix surfaced a tactic-level error at `right_inv` line 145: `rw [..., apply_symm_apply]` failed because `Real.Angle.toCircle z` and `homeomorphCircle' z` are only DEFINITIONALLY (not syntactically) equal — `rw` requires syntactic match. Fixed in the same iter by inserting a `change` step between the bridge `rw` and the `apply_symm_apply` `rw`, which converts `Real.Angle.toCircle z` → `homeomorphCircle' z` definitionally. Third run is in flight this iteration with the `change`-based fix.

**Iter 3 risks (logged 2026-06-06) status**: risk #1 (Real.Angle.toCircle unification) **CONFIRMED**: `left_inv`'s `exact homeomorphCircle'.symm_apply_apply x` worked because `exact` does definitional unification, but `right_inv`'s `rw [apply_symm_apply]` did not — needed `change` to convert syntactically. Risks #2 (Additive.ofMul_mul rfl) and #3 (right_inv rfl on `Additive.ofMul ∘ toMul = id`) are validated by the in-flight third run.

**Gallery entry drafted**: `src/data/proofs/euler-identity-oq-01-oq-04/meta.json` (status: verified, badge: original, 0 axioms, 0 sorries, lineCount 197, theoremCount 3, definitionCount 1) and `annotations.json` (5 section annotations covering the bridge lemma + AddEquiv + @[simp] API + sibling cross-reference). Section line ranges updated to match the post-fix file. Ship contingent on the in-flight build completing cleanly.

**Diff this iter**:
- `proofs/Proofs/EulerIdentityOQ01OQ04.lean`: 1-line import fix (`Mathlib.Topology.Instances.AddCircle` → `.Defs`) + 5-line `right_inv` fix (insert `change` between bridge `rw` and `apply_symm_apply` `rw`).
- `src/data/proofs/euler-identity-oq-01-oq-04/meta.json` (new file): full gallery metadata.
- `src/data/proofs/euler-identity-oq-01-oq-04/annotations.json` (new file): 5 annotations.
- `research/problems/euler-identity-oq-01-oq-04/state.md`: this block.

Session log: inline in state.md (no separate session file needed; the diff is small and surgical).


## Iter 3 ACT-2 (2026-06-06, researcher-1) — Sorry discharge via Real.Angle.toCircle bridge

Discharges the three named sorries from Iter 2's scaffold. The non-trivial step turned out to be: Mathlib v4.26.0's `AddCircle.toCircle` is a DIFFERENT `Periodic.lift` construction than `Real.Angle.toCircle`, even though both lift `Circle.exp` and are propositionally equal on representatives. The Iter 2 strategy table assumed they were definitionally equal — which would have made the discharge trivial (`exact homeomorphCircle'.symm_apply_apply x`), but actually a propositional bridge is required.

**Mathlib audit (raw GitHub source at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)**:
- `Real.Angle.toCircle θ := Circle.periodic_exp.lift θ` (line 98 of `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`) — direct lift of `Circle.exp` from `ℝ → Circle` to `Angle = AddCircle (2 * π) → Circle`.
- `AddCircle.toCircle (T) := (@scaled_exp_map_periodic T).lift` (line 138 of same file) — lifts `Circle.exp (2*π/T * x)`. At `T = 2*π`, `(2*π)/(2*π) = 1` propositionally (positivity), so `Circle.exp ((2π/2π) * x) = Circle.exp x` via `div_self + one_mul`.
- `AddCircle.homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle` has `toFun := Real.Angle.toCircle` (line 169) — NOT `AddCircle.toCircle`.

**Bridge lemma shipped**: `addCircle_toCircle_eq_angle_toCircle (x : AddCircle (2 * π)) : AddCircle.toCircle x = Real.Angle.toCircle x`. Proof: `QuotientAddGroup.induction_on`, then `rw [AddCircle.toCircle_apply_mk, div_self, one_mul]; rfl`. ~5 lines.

**Three discharges**:
- `left_inv x`: `rw [bridge]; exact homeomorphCircle'.symm_apply_apply x`.
- `right_inv y`: `rw [bridge, homeomorphCircle'.apply_symm_apply]; rfl`.
- `map_add' x y`: `show ...; rw [AddCircle.toCircle_add]; rfl`.

Total LOC added: ~45 (bridge lemma + 3 discharges + comments + docstring update). Net axiom/sorry count: 0 / 0.

**Build verification still deferred**: confirmed `proofs/.lake/packages/` returns "Too many levels of symbolic links" from this isolation worktree (same as the `szemeredi-full-oq-01` S10 sibling-slug observation). Build verification falls to the next ACT-3 iteration from main checkout (`./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04`), or to the auditor pipeline post-merge.

**Risks (this iter's best guesses; build will validate)**:
- `homeomorphCircle'.symm_apply_apply x` may need the unification `homeomorphCircle' x = Real.Angle.toCircle x` to hold by rfl (it should, since `toFun := Real.Angle.toCircle`).
- `Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b` is assumed to be `rfl` (since `Additive α := α` is a type alias and `Add (Additive α)` is defined as `Mul α` underlyingly). If not rfl, may need `Additive.ofMul_mul` rewrite or `rfl` may need to become `simp`.
- The `rfl` ending in `right_inv` (after `apply_symm_apply`) reduces to `Additive.ofMul (Additive.toMul y) = y`, which should be `rfl` for the same type-alias reason.

If any of these tactic-level guesses fail in the build, fixes are local (1-2 lines) and the file structure remains correct.

Session log: `sessions/2026-06-06-iter3-act2-sorry-discharge.md` (TBD if needed; the state.md block + session log inline above carries the authoritative context).



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

**Iteration 4 (Iter 3 ACT-2, this iter, researcher-1, 2026-06-06)**: Sorry discharge via `Real.Angle.toCircle` bridge. Adds 1 private bridge lemma and replaces 3 sorries with named-lemma chains. The discharge required revising the Iter 2 strategy table (which assumed `AddCircle.toCircle` and `Real.Angle.toCircle` were definitionally equal at `T = 2 * π`; they are propositionally equal but not definitionally — the `2π/2π = 1` reduction is not `rfl`).

**Highest-readiness next ACT — Iter 4 ACT-3 (next researcher, from main checkout)**: Run `./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04` to validate the 3 discharges + bridge lemma. If any tactic mismatches surface, they are local 1-2 line fixes (see "Risks" in Iter 3 ACT-2 block above). On clean build, add the gallery entry at `src/data/proofs/euler-identity-oq-01-oq-04/meta.json`.

## Active Approach

**Path A (recommended)**: Wrap `AddCircle.homeomorphCircle'` as `AddCircle (2 * π) ≃+ Additive Circle`. Defaults to ≃+ packaging (matches Mathlib's `Circle.expHom : ℝ →+ Additive Circle` convention).

**Path B (alternative, de-recommended)**: First isomorphism theorem on sibling's `circleHom : Multiplicative ℝ →* ℂˣ`. Documented as an educational follow-up if gallery owner wants the abstract-quotient-theorem connection.

## Attempt Count

- Total attempts: 2 (Iter 2 ACT-1 scaffold ship 2026-06-03; Iter 3 ACT-2 sorry discharge 2026-06-06)
- Current approach attempts: 2 (Path A scaffold-only ship + Path A sorry discharge)
- Approaches tried: 1 (Path A; Path B still de-recommended, available as alternate follow-up)

## Blockers

None on the math side. Build verification is the only remaining gating step.

**Soft persistent blocker**: this `.loom/worktrees/*` isolation worktree's `proofs/.lake/packages/` returns "Too many levels of symbolic links" (verified Iter 3 ACT-2 / 2026-06-06; same structural issue as `szemeredi-full-oq-01` S10's blocker note). Local `lake build` / Docker build from this worktree is not possible. Iter 4 ACT-3 must run from `/Users/rwalters/GitHub/lean-genius` (the main checkout), or rely on the post-merge auditor/mechanic pipeline.

## Next Action

Iter 4 ACT-3 (next researcher, from main checkout): (1) Run `./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04` to validate Iter 3 ACT-2's discharges; (2) if build fails, fix the local tactic-level issues flagged in Iter 3 ACT-2's "Risks" block (each is a 1-2 line fix; structure remains correct); (3) on clean build, ship the gallery entry at `src/data/proofs/euler-identity-oq-01-oq-04/meta.json` (status: `verified`, badge: `original`, 0 axioms, 0 sorries, lineCount and theoremCount per the file).
