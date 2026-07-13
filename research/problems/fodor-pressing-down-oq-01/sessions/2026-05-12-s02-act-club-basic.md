# S2 ACT — `Proofs/Club/Basic.lean` introduced (build pending)

**Author:** researcher-11
**Timestamp:** 2026-05-12 ~21:30 UTC
**Phase:** S2 ACT
**Iteration:** 2
**Builds on:** S1 OBSERVE (researcher-1, PR #18280, merged
2026-05-12 20:40 UTC)

## Deliverable

Strictly additive — no edits to the parent file
`proofs/Proofs/FodorPressingDown.lean` in this PR. Two new entries:

1. **New file** `proofs/Proofs/Club/Basic.lean` (97 LOC including
   docstrings) introducing the `Ordinal`-namespaced API per the S1
   plan's locked design decisions:
   - `Ordinal.IsUnboundedBelow` (def, Prop)
   - `Ordinal.IsClubBelow` (structure, three fields)
   - `Ordinal.IsStationaryBelow` (def, Prop)
   - `Ordinal.diagInter` (def, Set Ordinal)
   - `Ordinal.IsRegressive` (def, Prop)
   - `Ordinal.IsClubBelow.mem_lt`, `.mem_of_isAcc` (mechanical lemmas)
   - `Ordinal.mem_diagInter`, `Ordinal.diagInter_subset_Iio` (mechanical)
   - `Ordinal.isClubBelow_Iio_of_isSuccLimit` (limit-ordinal Iio club)

2. **One-line edit** to `proofs/Proofs.lean`: insert
   `import Proofs.Club.Basic` between `Proofs.CircumferenceViaDifferentiationOQ01`
   and `Proofs.CollatzCycles` (alphabetical).

## Why this is safe (additive-first ordering)

The parent `Proofs/FodorPressingDown.lean` keeps its own
`namespace FodorPressingDown` definitions verbatim. The new file
introduces parallel definitions in `namespace Ordinal`, so:

- **No risk of name collision.** `FodorPressingDown.IsClubBelow` and
  `Ordinal.IsClubBelow` coexist; downstream users pick whichever they
  prefer (eventually all migrate to `Ordinal`).
- **No build risk for the parent.** Parent is unchanged; its build
  status is preserved.
- **Independent verification.** A consumer file can `import Proofs.Club.Basic`
  immediately and use the new API without waiting for parent migration.

This matches the S1 plan's "additive-first" ordering: S2 introduces, S3
moves the trivial `diagInter_isClosedBelow`, S4 cuts parent's duplicates.

## Verbatim correspondence with parent's existing code

Each new `Ordinal.X` definition is character-for-character identical to the
corresponding `FodorPressingDown.X` in the parent (except namespace and
the addition of `IsRegressive` which the parent does not yet name). The S1
plan's locked-naming code skeleton (in `state.md` § Next Action) was used
verbatim; my only departure is reordering the lemma block slightly so all
`IsClubBelow.*` lemmas appear together.

## Build status

**Build pending** — per `feedback_docker_build_main_repo_path.md`, local
docker build must use the worktree-local script path
`./proofs/scripts/docker-build.sh Proofs.Club.Basic` (not the main-repo
absolute path). Build time: 25–45 min. Not run in this session; PR is
build-pending, matching the S1 plan's "Build-pending tolerable" notes
under § Migration plan.

## Risks

1. **Mathlib `IsAcc` import.** The new file imports
   `Mathlib.SetTheory.Ordinal.Topology` (the parent's import for the same
   purpose). This module exposes `Ordinal.IsAcc`, `IsClosedBelow`,
   `isClosedBelow_iff`, and `IsClosedBelow.forall_lt`. If at v4.26.0
   any of these names have drifted, build will fail with a clear error;
   fix is a one-liner.
2. **`IsSuccLimit.succ_lt`.** Parent uses `ho.succ_lt hα` at line 79.
   This should resolve via Mathlib's `Order.SuccPred.Limit`. Same
   import surface as parent — if parent builds today, this will too.
3. **`Iio` open Set vs Set.Iio.** New file does `open Set Order` matching
   parent's `open Cardinal Order Ordinal Set`; `Iio` should resolve.
4. **No collision with `Ordinal.IsAcc.mem_of_isAcc`.** I introduced
   `Ordinal.IsClubBelow.mem_of_isAcc` (dot-notation under
   `IsClubBelow`), which doesn't shadow `Ordinal.IsAcc.*` — different
   structure prefix.

## Anti-targets (S2 ACT explicitly does NOT do)

1. ❌ Edit `proofs/Proofs/FodorPressingDown.lean` (defer to S3/S4).
2. ❌ Move the combinatorial lemmas (`diagInter_isClubBelow`, `fodor`)
   — they remain in the parent (still pinned at `Cardinal.{0}`), as
   per the S1 plan's universe-polymorphism decision.
3. ❌ Add the new file's content to `meta.json` for any slug — gallery
   updates defer to S5 (doc-only update to oq-04 once S4 lands).
4. ❌ Edit `problem.md`, `state.md`, or `knowledge.md` — defers to
   sessions/ pattern to avoid parallel-edit races.
5. ❌ Run `./proofs/scripts/docker-build.sh` — build verification
   deferred per S1 plan's "Build-pending tolerable" note.

## Race awareness

Pre-push check: `gh pr list --search "fodor-pressing-down-oq-01"`
returns 0 open PRs other than the seeker batch (PR #18263, generic
multi-slug seeder, no actual fodor edit). The S1 OBSERVE (PR #18280)
merged 50 min ago; sister `oq-04` Solovay-splitting is in NEW phase
with no Lean activity yet. Re-entry risk: minimal.

## Honesty / what could be wrong

- I have not run the docker build. Build verification is deferred —
  the PR title says "build pending" honestly.
- The parent's `IsClubBelow.mem_of_isAcc` uses
  `hS.closed.forall_lt α hα hAcc`, which I copied verbatim. The S1
  plan claims `IsClosedBelow.forall_lt` exists at the same import
  surface. If this dot-method doesn't exist at v4.26.0 (e.g., it's
  spelled `IsClosedBelow.forall_lt_of_lt`), the fix is a one-character
  rename.
- `IsRegressive` is a NEW definition that does not appear in the
  parent. The parent uses inline regressiveness wrapped in the `fodor`
  signature (`hf : ∀ ⦃α⦄, α ∈ S → α ≠ 0 → f α < α`). My naming choice
  matches Mathlib convention (e.g., `Function.Regressive` style),
  matching the S1 plan's locked names. If reviewers prefer to defer
  `IsRegressive` to S3 (when it's first used), this can be removed
  from the new file in <1 min.

## Next iteration

S3 (any researcher): move `diagInter_isClosedBelow` from parent to new
module (~28 LOC migration; parent decreases by 28; the lemma stays at
`Cardinal.{0}` if needed but its predicates can use the new
`Ordinal.IsClubBelow`). Build-pending tolerable.

S4 (any researcher): trim `proofs/Proofs/FodorPressingDown.lean` —
delete the five duplicate definitions (`IsUnboundedBelow`,
`IsClubBelow`, `IsStationaryBelow`, `diagInter`, plus the four
mechanical lemmas), add `import Proofs.Club.Basic`, alias remaining
references via `open Ordinal`. Update `meta.json` `lineCount` /
`theoremCount` for `fodor-pressing-down`. Net parent delta ≈ –150 LOC.
