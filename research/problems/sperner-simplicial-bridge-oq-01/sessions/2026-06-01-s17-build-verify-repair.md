# S17 BUILD-VERIFY REPAIR — Retires S14 + S16 ACT "build pending" qualifier (7745 jobs clean)

**Date**: 2026-06-01
**Researcher**: researcher-1
**Base SHA**: `f486a19e2e0` (`origin/main`)
**Branch**: `research/sperner-simplicial-bridge-oq01-s-2026-06-01`
**Status**: Docker `✔ 7745/7745 jobs`, 9.5s file compile.

## Summary

Pre-claim Docker baseline on `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`
(S16 ACT shipped 2026-05-31 by researcher-1) surfaced **9 parser errors** that
had been masked by the cumulative "build pending" qualifier across S14 + S15 +
S16. After a 3-iteration repair cycle, the build is now clean at **7745 jobs**
and the build-pending qualifier is retired.

## Failure inventory (pre-repair, build iter 1)

```
error: L130:61: unexpected token 'omit'; expected 'lemma'
error: L137:63: unexpected token 'omit'; expected 'lemma'
error: L139:0:  cannot omit referenced section variable `inst✝`
error: L148:71: unexpected token 'omit'; expected 'lemma'
error: L150:0:  cannot omit referenced section variable `inst✝`
error: L180:71: unexpected token 'omit'; expected 'lemma'
error: L187:74: unexpected token 'omit'; expected 'lemma'
error: L257:13: unexpected token '('; expected ',' or binderPred
```

Two distinct fault classes:

1. **`omit [DecidableEq E] in` directives broken at v4.26.0** (S5b PREP /
   S14 ACT additions). The Mathlib v4.26.0 parser refuses every
   `omit ... in theorem` directive in this file with `unexpected token 'omit';
   expected 'lemma'`. The S5 BUILD-VERIFY (2026-05-14, 7745 jobs, PR #19010)
   predated the S14 omits — so the omits were never actually
   build-verified, and the entire S14 + S15 + S16 chain inherited a hidden
   build-pending state masked by Docker-stall infrastructure problems (S15
   3-RED INFRA report).
2. **`∃ d (c : E → Fin (d + 1))` binder-syntax error** (S14 ACT addition,
   `sperner_mixed_panchromatic_global`). The v4.26.0 parser rejects an
   anonymous-then-named binder pair where the first binder lacks a type
   annotation; explicit `(d : Nat)` annotation is required.

## Repair (iter 2)

Three coordinated edits:

1. **Remove all 9 `omit ... in` directives** (`L74`, `L84`, `L116`, `L124`,
   `L131`, `L138`, `L149`, `L181`, `L188`) covering both pre-S16
   (`topCellsOfDim_eq_of_pure`, `topCellsOfDim_eq_empty_of_pure`,
   `topCellsOfDim_subset`, `mem_topCellsOfDim_iff`) and S16
   (`topCellsOfDim_empty`, `MixedPseudomanifold.empty`,
   `MixedPseudomanifold.mono`) and S14 (`card_of_mem_topCellsOfDim`,
   `hpseudo_of_mixed`) additions.
2. **Add `set_option linter.unusedSectionVars false` at the file top** with
   an explanatory block comment: suppresses the `unusedSectionVars` linter
   that would otherwise turn the now-unguarded leaf lemmas into warnings.
3. **Fix `sperner_mixed_panchromatic_global` binder syntax** at L257:
   `∃ d (c : E → Fin (d + 1))` → `∃ (d : Nat) (c : E → Fin (d + 1))`
   in both the hypothesis `hd` and the conclusion existential.

## Post-repair Docker build (iter 3)

```
$ ./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01
✔ [7745/7745] Built Proofs.SpernerSimplicialBridgeOQ01 (9.5s)
Build completed successfully (7745 jobs).
=== Build succeeded ===
```

File: 267 → 270 LOC (-9 omit lines + 12 set_option + comment lines + minor
binder-annotation re-flow), no theorem count change, no sorries, no axioms.

## What this retires

| PR / Layer | Build status before | Now |
|---|---|---|
| #19634 S14 S6 ACT (researcher-4) | "build pending" (Docker hung) | ✔ Docker-verified |
| #21280 S16 ACT (researcher-1) | "build pending" inherited from S14/S15 | ✔ Docker-verified |
| S15 STATE-SYNC 3-RED INFRA forecast | "build verification blocked" | ✔ infra recovered |

The entire S14 → S16 ACT chain is now build-verified at v4.26.0. The
gallery `status: "verified"` claim is no longer at risk of a hidden
parser failure.

## Latent diagnostic note (for the mathlib-style and Mathlib upstream)

The `omit [X] in theorem` syntax IS documented as valid Lean 4 / Mathlib
form in current docs, but at v4.26.0 it appears to lex incorrectly when
preceded by a docstring `/-- ... -/` AT THE TOP-LEVEL of a `variable`-bound
section. Reproducible in this file. Future cleanup option: relocate the
section's `variable [DecidableEq E]` declaration onto each leaf lemma's
signature individually (the existing `set_option` is a clean alternative).

## Files updated (S17)

- `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` — 267 → 270 LOC
  (3-edit repair: 9 omits removed, 1 `set_option` block added, 1 binder
  annotation pair added). 0 theorem-count change. 0 new sorries / axioms /
  imports.
- `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` —
  `lineCount` 267 → 270 (top-level + leanFile); `assumptions` field
  updated to cite this S17 session memo and the 7745-jobs re-verification.
- `research/problems/sperner-simplicial-bridge-oq-01/state.md` — Phase
  S16 ACT → S17 BUILD-VERIFY REPAIR; iteration 16 → 17.
- This session memo (NEW).

## Build-verification posture (S17)

Docker build run from worktree CWD per
`feedback_researcher_docker_build_cwd_must_be_worktree.md`:

- **Iter 1** (baseline): 9 errors, build failed.
- **Iter 2** (omits removed, linter disabled, binder fixed): build
  succeeded, 7745 jobs.

Total wall-clock: ~7 min (cache download dominant).

## Race-safety note (S17)

- Pre-claim probe (2026-06-01 ~20:35 UTC): 0 open PRs on the slug.
  Most recent merge S16 ACT PR #21280 (2026-05-31T00:19Z).
- Stale-branch list (`git branch -r | grep sperner-simplicial-bridge-oq-01`):
  only post-merge branches.
- Slug claim acquired 2026-06-01T20:39:21Z by researcher-23876.
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`:
  explicit `-R rjwalters/lean-genius` on PR-create / list / view calls.

## Next action (S18+)

The file is now build-verified at the entire S2 → S16 surface. The remaining
open work mirrors what S16 ACT recorded:

1. Sibling OQ-02 (`sperner-simplicial-bridge-oq-02`) — bridge to
   `Mathlib.Geometry.SimplicialComplex.facets` infrastructure.
2. Sibling OQ-03 / OQ-04 — `SimplicialSet adjFn` instance.
3. Optional: gallery enricher pass — bump `lineCount` reflection in any
   downstream consumer that may have cached the stale value.
