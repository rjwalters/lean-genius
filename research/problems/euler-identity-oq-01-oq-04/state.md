# Research State: euler-identity-oq-01-oq-04

## Current State
**Phase**: DECIDE (Iter 1 ORIENT/PREP — Mathlib bearer audit + paste-ready isomorphism wrapper sketch SHIPPED doc-only; ready for Iter 2 ACT)
**Path**: full
**Since**: 2026-04-05T19:03:34-07:00 (initial selection; first substantive iteration 2026-06-01)
**Last Updated**: 2026-06-01 (Iter 1 ORIENT/PREP — bearer audit; iteration 1→2; no Lean edits, no axiom/sorry delta, researcher-1)
**Iteration**: 2

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

**Iteration 2 (Iter 1 ORIENT/PREP, this iter, researcher-1, 2026-06-01)**: Doc-only ORIENT-to-DECIDE advance. Maps Mathlib v4.26.0 API drift since 2026-04-05 selection, reads sibling Lean files, identifies the precise packaging gap (Mathlib has `≃ₜ`, not `≃+`), and provides a paste-ready ~20-LOC wrapper sketch (Path A) plus an alternative ~50-LOC quotient-theorem route (Path B). No Lean changes; sibling file `EulerIdentityOQ01OQ01OQ01.lean` already proves all underlying lemmas axiom-free.

**Highest-readiness next ACT — Iter 3 (next researcher)**: Apply the Path A paste-ready skeleton to a new file `proofs/Proofs/EulerIdentityOQ01OQ04.lean` (or extend `EulerIdentityOQ01OQ01OQ01.lean` if the gallery prefers in-file expansion). Discharge three sorries (`left_inv`, `right_inv`, `map_add'`) via `simp` chains over existing Mathlib + sibling lemmas. Build-verify under `./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04`. Expected ACT cost: ~15-25 LOC.

## Active Approach

**Path A (recommended)**: Wrap `AddCircle.homeomorphCircle'` as `AddCircle (2 * π) ≃+ Additive Circle`. Defaults to ≃+ packaging (matches Mathlib's `Circle.expHom : ℝ →+ Additive Circle` convention).

**Path B (alternative, de-recommended)**: First isomorphism theorem on sibling's `circleHom : Multiplicative ℝ →* ℂˣ`. Documented as an educational follow-up if gallery owner wants the abstract-quotient-theorem connection.

## Attempt Count

- Total attempts: 0 (no Lean writes yet; PREP-only)
- Current approach attempts: 0
- Approaches tried: 0 (Path A and Path B sketched but no ACT)

## Blockers

None. All Mathlib bearers pinned to verbatim source at SHA `2df2f0150c…`. Sibling file `EulerIdentityOQ01OQ01OQ01.lean` proves all underlying lemmas axiom-free. The ACT is a packaging exercise (~15-25 LOC), not a mathematical-content gap.

**Soft open question**: gallery-owner preference between Path A (≃+ packaging, default) and Path B (≃* / first-isomorphism-theorem packaging, more abstract). Default recommendation: Path A.

## Next Action

Iter 3 ACT: Path A wrapper. Create `proofs/Proofs/EulerIdentityOQ01OQ04.lean` with `addCircleEquivAdditiveCircle : AddCircle (2 * π) ≃+ Additive Circle`. Discharge three sorries with `simp` chains over `AddCircle.homeomorphCircle'`, `AddCircle.toCircle_add`, `AddCircle.toCircle_zero`, and `Additive.ofMul/toMul` reductions. Build-verify under Docker.
