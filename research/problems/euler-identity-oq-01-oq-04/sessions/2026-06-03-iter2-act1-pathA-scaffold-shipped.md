# Iteration 2 ACT-1 — Path A wrapper scaffold shipped

**Date**: 2026-06-03
**Researcher**: researcher-1
**Phase**: DECIDE → ACT (Iter 2 ACT-1 within the slug)
**Type**: First Lean edit on this slug. Ships the Path A wrapper file
with three named sorries (`left_inv`, `right_inv`, `map_add'`)
following the paste-ready skeleton from the 2026-06-01 Iter 1 ORIENT/
PREP session log.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0 toolchain; same SHA the Iter 1 PREP audited).
**Base HEAD**: `e89e9e882e18d0ae3f23e9601b0f185ec154fba9` (current
`main`, build-perf phase-2 landing).

## Rationale

The 2026-06-01 Iter 1 ORIENT/PREP session log
(`sessions/2026-06-01-iter1-orient-prep-mathlib-bearer-audit.md`)
concluded with a paste-ready ~15-25 LOC Path A skeleton and recommended
the next researcher (Iter 2 ACT or, in their original numbering, "Iter
3 ACT") apply it to a new file
`proofs/Proofs/EulerIdentityOQ01OQ04.lean`.

This iteration ships that file. It is **scaffold-only**: the three
named tactic obligations are left as `sorry` with explicit named-Mathlib-
lemma discharge strategies in comments. The structural skeleton — the
`AddEquiv` record, the `toFun`/`invFun` choices, and the `@[simp]` API
lemmas — compiles in principle against the Mathlib v4.26.0 API the
prior PREP pinned.

## Why scaffold-only (build verification deferred)

The local Docker environment in this researcher worktree session was
not in a fit state to run `./proofs/scripts/docker-build.sh
Proofs.EulerIdentityOQ01OQ04` end-to-end:

1. The local Docker image `lean4-arm64:v4.26.0` is missing; rebuilding
   it from `proofs/Dockerfile` would dominate the iteration budget.
2. The host Docker has a corrupted blob (one image-list query returned
   "input/output error" on a content-addressed blob), so a clean image
   rebuild requires Docker-side maintenance the researcher loop should
   not perform without operator confirmation.
3. The worktree's `proofs/.lake` symlink is self-referential (points
   to itself in the main repo), so direct `lake build` is also not
   wired — and the project's CLAUDE.md hard-blocks `lake build`
   anyway.

Rather than block the iteration, the scaffold is shipped with three
sorries explicitly named in the docstring, each annotated with the
discharge strategy. The next researcher (Iter 3 ACT-2) or an Aristotle
companion job can run docker-build and discharge the three sorries with
the 1-3 line `simp` chains already pinned in the file's comments.

This matches the gallery's convention of incremental progress: 1
sorry-bearing companion file is acceptable (cf.
`EulerIdentityOQ01OQ01.lean` which currently has 1 sorry per the
registry's `leanFiles[]` metadata).

## What this iteration ships

**New file**: `proofs/Proofs/EulerIdentityOQ01OQ04.lean` (~125 LOC,
including ~65 LOC of docstring/strategy comments).

**Definition**:
```lean
noncomputable def addCircleEquivAdditiveCircle :
    AddCircle (2 * π) ≃+ Additive Circle where
  toFun x := Additive.ofMul (AddCircle.toCircle x)
  invFun y := AddCircle.homeomorphCircle'.symm (Additive.toMul y)
  left_inv := /- sorry: see file comments -/
  right_inv := /- sorry: see file comments -/
  map_add' := /- sorry: see file comments -/
```

**API lemmas** (both `@[simp]`, both `rfl`-provable):
* `addCircleEquivAdditiveCircle_apply` — forward = `Additive.ofMul ∘
  AddCircle.toCircle`.
* `addCircleEquivAdditiveCircle_symm_apply` — inverse =
  `AddCircle.homeomorphCircle'.symm ∘ Additive.toMul`.

**Status counter**: 0 axioms, 3 sorries (`left_inv`, `right_inv`,
`map_add'`). All three sorries are inside the `AddEquiv` record,
labeled in comments with the Mathlib lemma each invocation should chain
through.

## Discharge strategies (for Iter 3 ACT-2)

| Sorry | Goal | Suggested tactic |
|---|---|---|
| `left_inv` | `AddCircle.homeomorphCircle'.symm (AddCircle.toCircle x) = x` | Identify `AddCircle.toCircle x` with `AddCircle.homeomorphCircle' x` (via `@[simps]`-generated `coe_toFun` or a direct `rfl`), then apply `Homeomorph.symm_apply_apply` / `homeomorphCircle'.left_inv`. |
| `right_inv` | `Additive.ofMul (AddCircle.toCircle (AddCircle.homeomorphCircle'.symm y.toMul)) = y` | Apply `homeomorphCircle'.right_inv` (after the same toFun identification), then collapse `Additive.ofMul ∘ Additive.toMul = id`. |
| `map_add'` | `Additive.ofMul (AddCircle.toCircle (x + y)) = Additive.ofMul (AddCircle.toCircle x) + Additive.ofMul (AddCircle.toCircle y)` | `rw [AddCircle.toCircle_add]` then `rfl` (since `Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b` by definition). |

Expected total discharge LOC: 3-8 lines across the three sorries.

## What this iteration does NOT ship

1. **No build verification** — see "Why scaffold-only" above. The next
   researcher MUST run `./proofs/scripts/docker-build.sh
   Proofs.EulerIdentityOQ01OQ04` and adjust any tactic mismatches.
2. **No sorry discharge** — three sorries shipped intentionally as
   tactic-skeleton placeholders.
3. **No gallery-side updates** — no `src/data/proofs/euler-identity-*/`
   edits. Those are downstream of a sorry-clean `Proofs.EulerIdentityOQ01OQ04`
   build.
4. **No `problem.md` or `knowledge.md` rewrite** — same template-
   placeholder state flagged by the Iter 1 PREP; documentation pass
   deferred to a separate iteration.
5. **No Path B exploration** — Path A is the recommended route; Path B
   remains documented as a follow-up educational PREP if the gallery
   owner requests it.

## Honest framing / self-audit

* **First Lean edit on this slug.** Selection-to-now: 2026-04-05 (OBSERVE) →
  2026-06-01 (Iter 1 ORIENT/PREP doc-only) → 2026-06-03 (Iter 2 ACT-1
  scaffold, this iteration). 58 days from selection to first Lean
  artifact.
* **Build-unverified.** The file's tactic content is best-guess based on
  the Iter 1 PREP's audit. The structural skeleton matches Mathlib's
  named bearers verbatim, but tactic alignment (e.g.,
  `homeomorphCircle'.toFun` vs `AddCircle.toCircle` syntactic match) is
  the kind of thing that fails on the first build attempt and is fixed
  in 1-2 minutes by a `change`/`show` rewrite. Iter 3 ACT-2 should
  expect to spend 5-15 min on tactic polish, not novel mathematics.
* **Three sorries is intentional.** Shipping the scaffold lets the next
  iteration focus narrowly on tactic discharge with full Docker access,
  rather than re-deriving the whole packaging architecture.
* **No claim of completion.** The slug's `currentState` should remain
  `ACT (Iter 2 ACT-1 scaffold shipped, build verification + sorry
  discharge pending)`, not `completed` / `solved`. The `status` field
  in the JSON stays `active`.

## Cross-references

* **Iter 1 ORIENT/PREP session log**:
  `sessions/2026-06-01-iter1-orient-prep-mathlib-bearer-audit.md` —
  the audit + paste-ready skeleton this iteration applies.
* **Sibling Lean file**:
  `proofs/Proofs/EulerIdentityOQ01OQ01OQ01.lean` — axiom-free Lie-group
  hom on `Multiplicative ℝ →* ℂˣ`; this slug packages the Mathlib-
  `Circle` analogue.
* **Mathlib bearer**:
  `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean:168`
  (`AddCircle.homeomorphCircle'`) at SHA `2df2f0150c…` — the topological
  bijection this slug upgrades to a `≃+`.
* **Mathlib homomorphism lemma**:
  `Mathlib/IntervalIntegral/.../Circle.lean:144`
  (`AddCircle.toCircle_add`) — the lemma the `map_add'` sorry chains
  through.

## What the next researcher should do (Iter 3 ACT-2)

1. Run `./proofs/scripts/docker-build.sh Proofs.EulerIdentityOQ01OQ04`.
2. If the file structure fails to parse, fix syntactic mismatches
   (likely just `AddEquiv` field-order or `Additive` namespace
   resolution).
3. Discharge the three sorries using the per-sorry strategy table above.
4. Update `state.md` to "Iter 3 ACT-2 sorry discharge complete, file
   builds clean" with the final LOC count.
5. Update the JSON's `leanFiles[]` entry for this file (line count,
   theorem count, sorry count = 0 if discharge succeeded).
6. Consider whether to advance `status` from `active` to `completed`
   (probably yes, once 0 sorries and gallery integrity is verified).
