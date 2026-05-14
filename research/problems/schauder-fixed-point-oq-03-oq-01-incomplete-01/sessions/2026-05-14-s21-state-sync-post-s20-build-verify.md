# S21 STATE-SYNC (researcher-9, 2026-05-14, doc-only)

## Trigger

S20 ACT (PR #19016, OPEN/MERGEABLE/CLEAN as of 2026-05-14T08:50Z) shipped
five surgical Mathlib v4.26.0 fixes inside `exists_continuous_proj_convex`
(the S14-landed Hilbert-projection helper, file lines ~211–305). The PR
was **build-verified** locally (Docker wrapper, 3074-job clean build),
ending the S11→S19 ACT "build pending" chain that had run since
2026-05-08. Both `state.md` and the slug JSON
(`src/data/research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01.json`)
froze at earlier iterations and need refreshing.

- `state.md` last refresh: S19a-ACT (researcher-11, 2026-05-13T07:15Z).
  Calls itself "(this PR)" for S19a-ACT and is missing both the S19a-ACT
  merge fact (#18646, merged 2026-05-13T08:09Z) and the S20 entry.
- `currentState.focus` in JSON: even more stale — still describes S18f
  (researcher-10, 2026-05-12), four iterations behind S20.
- `currentState.iteration`: 23, but no `lastUpdated` field; top-level
  `lastUpdate`: 2026-05-11T17:55Z.

## What S20 ACT (PR #19016) did

Five edits inside `exists_continuous_proj_convex` (Lean file lines
~227–308), totalling +28 / −13 (lineCount 1218 → 1233):

1. **Add `open scoped InnerProductSpace`** (above the namespace block,
   new lines ~57–63): the `⟪x, y⟫_ℝ` real-inner-product notation
   migrated to `scoped[InnerProductSpace]` under v4.26.0; the
   deprecated `Mathlib.Analysis.InnerProductSpace.Projection` monolith
   used to bring it in transitively, and the import surface no longer
   does. Without `open scoped`, the proof body fails to parse.

2. **Add `haveI : Nonempty ↥S := hS_ne.to_subtype`** (new line ~230 at
   the top of the proof body): `le_ciInf` / `ciInf_le` now require the
   `[Nonempty ↥S]` instance to be in the local context explicitly
   rather than auto-deriving it from `S.Nonempty` inside the proof.

3. **Explicit subtype coercion in `set v₁/v₂`** (lines ~263–266):
   `(r u₁ : _)` no longer auto-coerces `↥S → EuclideanSpace ℝ (Fin n)`
   in the RHS of `set`. Refactor to `(↑(r u₁) : EuclideanSpace ℝ (Fin n))`
   (explicit subtype coercion via `↑`).

4. **Swap `real_inner_comm v₂ v₁` → `real_inner_comm v₁ v₂`** (line
   ~276): the v4.26.0 convention flipped — `real_inner_comm x y` now
   produces `⟪y, x⟫ = ⟪x, y⟫`, opposite of the old call.

5. **Refactor 1-Lipschitz argument via `LipschitzWith.mk_one`**
   (lines ~295–308): the `dist (... : ↥S) ≤ ((1 : ℝ≥0) : ℝ) * dist u₁ u₂`
   formulation triggered a `Type`-kind metavariable in v4.26.0's
   elaboration of `LipschitzWith.of_dist_le_mul`. Refactor to name the
   underlying function `f := fun u => Subtype.val (r u)`, drop the
   `ℝ≥0`-cast machinery, and use `LipschitzWith.mk_one` (the `K = 1`
   specialization that takes `dist (f u₁) (f u₂) ≤ dist u₁ u₂` directly).

The fix kit ships under
`feedback_researcher_mathlib_v426_subtype_lipschitz_innerproduct_kit.md`
in my MEMORY.md — full text of the diagnoses and patches.

## Build-verification evidence

- PR #19016 `.loom/logs/researcher-9-schauder-s20-act-build*.log`:
  `Build completed successfully (3074 jobs)`.
- `gh pr view 19016 -R rjwalters/lean-genius --json mergeable,mergeStateStatus`
  at 2026-05-14T08:50Z: `MERGEABLE` / `CLEAN`. Awaiting deployer (math
  PRs are merged by deployer, not Loom Judge — see CLAUDE.md "PR Labels
  for Math Agents").

## Scope of this STATE-SYNC

1. **state.md**: refresh header (Current State block, line 4–7),
   prepend a new "Current Focus" entry describing S20 ACT, update Open
   PRs (PR #19016 as OPEN/MERGEABLE/CLEAN), and extend Iteration
   History with two new rows: S19a-ACT merge fix-up (researcher-11, PR
   #18646 merged 2026-05-13T08:09Z) and S20 ACT (researcher-9, PR
   #19016 OPEN, build verified 3074 jobs).

2. **JSON**: refresh top-level `lastUpdate` to 2026-05-14, refresh
   `currentState.focus` and `currentState.nextAction` to reflect the
   S20-verified state, bump `currentState.iteration` from 23 to 25
   (S19a-ACT = 24, S20 ACT = 25; this STATE-SYNC is doc-only and does
   not get a Lean-iteration number), and add a `currentState.lastUpdated`
   field set to the current ISO 8601 timestamp. Top-level `phase` stays
   `ACT` (still discharging `axiom approx_selection_exists` via S19 step
   (b)/(c)/(d)).

3. No Lean-file modifications. No meta.json touch (no
   `src/data/proofs/schauder-fixed-point-oq-03-oq-01-incomplete-01/`
   directory exists for this slug — meta lives only under the parent
   `schauder-fixed-point-oq-03-oq-01` gallery entry, which is not in
   scope here).

## Next-after-this-PR Action (unchanged, just clarified)

The S19 step (a) closed-image helper (PR #18646) and the S14 helper
build-verification (S20 ACT, PR #19016) leave the path to discharging
`axiom approx_selection_exists` unchanged:

- **S19 step (b)** (~80–150 lines): §4.b nearest-point projection /
  convex-image construction chaining the S19a closed-image helper
  through `exists_norm_eq_iInf_of_complete_convex` and the S18e
  witness bundle.
- **S19 step (c)** (~30–60 lines): §5 graph-distance bound chaining
  S18f input-ball + S18e selector + §4.b projection.
- **S19 step (d)** (~10–20 lines): final packaging — `theorem
  approx_selection_exists_proof` replaces `axiom approx_selection_exists`.

`axiom brouwer_unit_ball` remains out-of-scope (in-house Brouwer FPT
would be very large; Mathlib v4.26.0 lacks it entirely per S10
findings).

## STATE-SYNC budget cap

This is STATE-SYNC #1 of this researcher-9 session. Per the
two-per-session cap (memory), I have one remaining; reserved for a
post-#19016-merge follow-up that retires the "(build pending)"
qualifier across `progressSummary` and `builtItems` once the PR lands
on main.
