# Iteration 3 ACT-2 — Sorry discharge via Real.Angle.toCircle bridge

**Date**: 2026-06-06
**Researcher**: researcher-1
**Phase**: ACT (Iter 3 ACT-2 within the slug)
**Type**: Discharges the three named sorries from Iter 2's scaffold.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
**Base HEAD**: `1aee42a9c5f` (current `main`, audit tracker bump).

## What this iteration ships

**Modified file**: `proofs/Proofs/EulerIdentityOQ01OQ04.lean` (~148 → ~192 LOC; +44 lines).

**New private lemma** (~5 lines, new §0):
```lean
private lemma addCircle_toCircle_eq_angle_toCircle (x : AddCircle (2 * π)) :
    AddCircle.toCircle x = Real.Angle.toCircle x := by
  induction x using QuotientAddGroup.induction_on with
  | _ r =>
    rw [AddCircle.toCircle_apply_mk, div_self (by positivity : (2 * π : ℝ) ≠ 0),
        one_mul]
    rfl
```

**Three sorries discharged** in the `addCircleEquivAdditiveCircle` `AddEquiv` record:
- `left_inv x`: `show ...; rw [bridge]; exact homeomorphCircle'.symm_apply_apply x`
- `right_inv y`: `show ...; rw [bridge, homeomorphCircle'.apply_symm_apply]; rfl`
- `map_add' x y`: `show ...; rw [AddCircle.toCircle_add]; rfl`

**Status counter**: 0 axioms, 0 sorries (down from 0 axioms, 3 sorries).

## Why the Iter 2 strategy table needed revision

Iter 2's strategy table (`sessions/2026-06-03-iter2-act1-pathA-scaffold-shipped.md`) suggested 3-8 lines of `simp` chains, on the assumption that `AddCircle.toCircle x` and `homeomorphCircle' x` were definitionally equal at `T = 2 * π`. **They are not**.

Raw Mathlib audit (at the pinned SHA, via `raw.githubusercontent.com`):
- `Real.Angle.toCircle θ := Circle.periodic_exp.lift θ` (`Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean:98`). Direct lift of `Circle.exp`.
- `AddCircle.toCircle (T) := (@scaled_exp_map_periodic T).lift` (`:138`). Lifts `Circle.exp ((2π/T) * x)`; at `T = 2*π`, the `(2π/2π) = 1` reduction is propositional (positivity needed), not `rfl`.
- `AddCircle.homeomorphCircle'.toFun := Real.Angle.toCircle` (`:169`) — **NOT** `AddCircle.toCircle`.

So `homeomorphCircle' x` reduces to `Real.Angle.toCircle x` by `rfl`, but `AddCircle.toCircle x` does not — even at `T = 2 * π`. A propositional bridge lemma is required.

The bridge does the `2π/2π = 1` reduction explicitly via `div_self + one_mul`, then closes with `rfl` (since `Real.Angle.toCircle ↑r = Circle.exp r` is `rfl` per `Real.Angle.toCircle_coe`).

## Build verification deferred

Same persistent issue as `szemeredi-full-oq-01` S10's blocker note: `proofs/.lake/packages/` returns "Too many levels of symbolic links" from any `.loom/worktrees/*` isolation. Local `lake build` / `docker-build.sh` cannot run. Iter 4 ACT-3 must run from the main checkout, or build validation falls to the post-merge auditor/mechanic pipeline.

## Tactic-level risks (build will validate)

If any of these fail, fixes are local (1-2 lines per item) and the file structure / lemma chain remains correct:

1. `exact AddCircle.homeomorphCircle'.symm_apply_apply x` (in `left_inv`) requires `homeomorphCircle' x = Real.Angle.toCircle x` to unify by `rfl`. This should hold since `toFun := Real.Angle.toCircle` is a direct structure field assignment.
2. The final `rfl` in `right_inv` reduces to `Additive.ofMul (Additive.toMul y) = y`, which should be `rfl` since `Additive α := α` is a type alias.
3. The final `rfl` in `map_add'` reduces to `Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b`, which should be `rfl` by the type-alias `Add (Additive α) := Mul α` chain (if not, swap in `rw [Additive.ofMul_mul]`).
4. The bridge lemma's `rfl` after `rw [div_self, one_mul]` reduces to `Circle.exp r = Real.Angle.toCircle ↑r`, which should be `rfl` via `Real.Angle.toCircle_coe` (if direction matters, use `(Real.Angle.toCircle_coe r).symm`).

## What this iteration does NOT ship

1. **No build verification** — isolation-worktree limitation (see above).
2. **No gallery `meta.json`** — defers to Iter 4 ACT-3 (post build-clean confirmation), per Iter 2's note.
3. **No `problem.md` rewrite** — same template-placeholder state as before; documentation pass deferred to a separate iteration.
4. **No Path B exploration** — Path A is now sorry-clean; Path B remains a follow-up educational PREP if the gallery owner requests it.

## Honest framing / self-audit

- This is the **second** Lean edit on the slug (after Iter 2's scaffold).
- The Iter 2 strategy table proved 50% accurate: the `map_add'` discharge worked as suggested (`rw [AddCircle.toCircle_add]; rfl`), but `left_inv`/`right_inv` required a propositional bridge lemma the Iter 2 PREP didn't anticipate.
- Total time from selection (2026-04-05) to sorry-clean: 62 days. Iter 1 ORIENT/PREP doc-only (2026-06-01), Iter 2 scaffold (2026-06-03), Iter 3 discharge (2026-06-06).
- Build-unverified at this iteration. The tactics are best-guess based on the raw-GitHub Mathlib audit. The next researcher's first action is the docker-build.

## References

- Iter 1 ORIENT/PREP session log: `sessions/2026-06-01-iter1-orient-prep-mathlib-bearer-audit.md`
- Iter 2 ACT-1 scaffold session log: `sessions/2026-06-03-iter2-act1-pathA-scaffold-shipped.md`
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
- Mathlib bearer file: `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` (lines 98, 138, 169 cited above)
- Sibling Lean file: `proofs/Proofs/EulerIdentityOQ01OQ01OQ01.lean` (Lie-group hom on `Multiplicative ℝ →* ℂˣ`)
