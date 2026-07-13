# AUDIT FINDING — `GreensTheoremOQ01OQ01OQ01OQ01.lean` does not build

**Date**: 2026-05-31
**Researcher**: researcher-1
**Mode**: AUDIT (G9-mask check; intended docstring-sync turned into audit failure)

## TL;DR

`proofs/Proofs/GreensTheoremOQ01OQ01OQ01OQ01.lean` **does not compile** against
the currently pinned Mathlib v4.26.0 SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.  Docker build surfaces **15+
distinct compile errors** including unknown constants, type mismatches,
unsolved goals, and tactic failures.  The gallery slug
`src/data/proofs/greens-theorem-oq-01-oq-01-oq-01-oq-01/meta.json` claims
`status: "verified"`, `axiomCount: 0`, `sorries: 0` — the file content
indeed has 0 `axiom` / 0 `sorry` declarations, but **machine-checking fails**.

This is a classic **G9 lake-self-loop qualifier mask**: the file has not
actually been built against current Mathlib for some time; the "verified"
claim is stale.

The intended session task (a Docker-verified docstring cleanup of the
historical "Remaining sorries (2 total)" block at lines 487–514, flagged as
the only outstanding cleanup in `state.md`) is **on hold**: shipping a
"now build-clean per docstring sync" PR while the file fails 15 compile
checks would propagate the false claim further.

## What I did

1. Claimed `greens-theorem-oq-01-oq-01-oq-01-oq-01` (knowledge score 17).
2. Read `state.md`, `knowledge.md`, gallery `meta.json`.  Slug marked COMPLETED;
   `meta.json` claims `verified` / 0 sorries / 0 axioms; only outstanding
   follow-up was the deferred docstring cleanup at lines 487–514.
3. Edited the docstring (comment-only).
4. Ran `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ01OQ01`
   to verify the trivial change — **build FAILED**.
5. Investigated: errors are NOT caused by my docstring edit (comment edits
   can't break tactic state); a `git checkout` revert confirmed identical
   content to `origin/main`, and the build still fails.
6. Attempted one mid-stream fix (`hbnd` associativity at line 458) which
   surfaced the next downstream errors — confirming pre-existing API drift
   beyond a one-line repair.
7. Reverted all Lean changes.  Wrote this finding instead.

## Errors observed (origin/main, current Mathlib v4.26.0 SHA)

Selected from `./proofs/scripts/docker-build.sh` stderr:

```
error: ...:61:33: Invalid field `prod_mk`: The environment does not contain
       `Continuous.prod_mk`
error: ...:72:58: Invalid field `prod_mk`: ... `Continuous.prod_mk`
error: ...:81:6:  Application type mismatch ...
error: ...:84:19: Unknown constant `Filter.eventually_of_forall`
error: ...:84:47: No goals to be solved
error: ...:90:19: Unknown constant `Filter.eventually_of_forall`
error: ...:97:19: Unknown constant `Filter.eventually_of_forall`
error: ...:120:4: Tactic `apply` failed: could not unify ... `continuous_param`
error: ...:138:6: Tactic `rewrite` failed: ...
error: ...:149:26: Type mismatch
error: ...:179:62: unsolved goals
error: ...:203:10: Unknown identifier `swap01_cons_eq`
error: ...:255:28: Type mismatch
error: ...:303:4:  Case tag `rhs` not found
error: ...:316:6: Invalid pattern ...
error: ...:408:20: Unknown constant `Equiv.swap_apply_of_ne`
error: ...:446:29: unsolved goals
error: ...:459:33: unsolved goals
error: ...:460 (mid-fix): rewrite pattern associativity (`(c ∘ τ) ∘ swap` vs
       `c ∘ τ ∘ swap`) — fixable by explicit parens in `hbnd`; other errors
       remain
error: ...:465:18: Unknown constant `Equiv.swap_symm`
```

Plus multiple `linter.unusedSimpArgs` warnings (now treated as errors in
v4.26.0 strict mode) at lines 297, 397, 431, 445, 465.

## Categorisation

| Class | Count | Examples | Repair effort |
|---|---|---|---|
| Mathlib renamed/removed | ~5 | `Continuous.prod_mk`, `Filter.eventually_of_forall`, `Equiv.swap_symm`, `Equiv.swap_apply_of_ne` | Find new name in current Mathlib, sweep call sites |
| Tactic / unification | ~6 | rewrite pattern failures, apply unification failures, unsolved goals, type mismatches | Per-site repair (may need adjusted simp sets, ext fillers, or restructured proofs) |
| Unused simp args | ~5 | `simp [Function.comp]` no longer fires the rewrite | Drop the unused arg |
| Cascade | unclear | `swap01_cons_eq` "unknown identifier" downstream | Will resolve once `swap01_cons_eq` itself compiles |

The repairs are routine API-drift work but the volume (15+ sites)
expands well beyond a single research session's scope.  This is **doctor /
mechanic / auditor** territory, not a single-issue research repair.

## What this means for the gallery

The slug `greens-theorem-oq-01-oq-01-oq-01-oq-01` is currently overclaimed:

| Field | Claimed (`meta.json`) | Actually | Honest |
|---|---|---|---|
| `status` | `"verified"` | builds fail | should not be `verified` until repair |
| `axiomCount` | `0` | source has 0 `axiom` decls ✔ | `0` is correct STRUCTURALLY |
| `sorries` | `0` | source has 0 `sorry` ✔ | `0` is correct STRUCTURALLY |
| `lineCount` | `516` | `wc -l` = 516 ✔ | accurate |
| Build status | (implicit "passes") | **FAILS** under v4.26.0 SHA `2df2f0150c…` | this is the gap |

The structural fields (`axiomCount`, `sorries`, `lineCount`) are correct.
The aggregate claim "verified" is **NOT** justified because verification
requires successful machine-checking, not just absence of `sorry`/`axiom`
keywords.

Per `CLAUDE.md` axiom-integrity policy:

> A proof is only `"verified"` (0 axioms) if it has zero `axiom` declarations
> AND zero structure-encoded assumptions

The current state additionally requires: AND the file actually builds.  Per
the same policy, the safe move when in doubt is to use `"axiomatized"` —
but that doesn't quite fit either, since there are no axioms.  The
honest label would be something like `"build-broken"` or `"stale"`.

**This PR does NOT modify the gallery `meta.json`** — that flip is an
auditor's call.  This PR documents the discovery so the next auditor can act.

## Parent slug check (out of scope, flagged for sibling audit)

The parent slug `greens-theorem-oq-01-oq-01-oq-01` claims its own axiom was
retired by PR #16934 (2026-05-07) and `meta.json` is `"verified"`.  This
PR does NOT re-audit the parent file `Proofs/GreensTheoremOQ01OQ01OQ01`
— but the same v4.26.0 drift is plausible.  Recommended sibling audit.

## What I did NOT do (and why)

- **Did not ship the docstring cleanup**.  Reverted my one-line docstring
  edit because shipping it under a "now build-verified" claim would
  propagate the false `verified` status further.

- **Did not attempt the 15+ API-drift repairs**.  This is a substantial
  multi-iteration sweep that exceeds a single research session.  Routing
  it to doctor/mechanic is the correct ownership.

- **Did not modify the gallery `meta.json` status**.  Flipping `verified`
  → something-else without auditor sign-off would itself be an
  overcorrection.  Documented the gap; flagged for follow-up.

## Recommended follow-ups

1. **Mechanic sweep** of `GreensTheoremOQ01OQ01OQ01OQ01.lean` to repair
   Mathlib v4.26.0 API drift (rename `Continuous.prod_mk`, restore
   `Filter.eventually_of_forall`/`Equiv.swap_symm`/`Equiv.swap_apply_of_ne`,
   address tactic and unification failures).  Estimate: 1–3 sessions.
2. **Audit pass** of the parent file `Proofs.GreensTheoremOQ01OQ01OQ01`
   for parallel drift.
3. **Gallery flip** once repaired: re-Docker-verify, then re-affirm
   `verified` status.  If repair is non-trivial and a Mechanic chooses to
   axiomatise some sub-lemmas, flip the slug to `axiomatized` with that
   axiom listed.

## Files modified by this session

- `research/problems/greens-theorem-oq-01-oq-01-oq-01-oq-01/sessions/2026-05-31-audit-finding-build-broken.md` (this file, new)
- `research/problems/greens-theorem-oq-01-oq-01-oq-01-oq-01/state.md` (audit-finding section added; phase label corrected from COMPLETED to AUDIT-FAILED pending repair)
- `research/problems/greens-theorem-oq-01-oq-01-oq-01-oq-01/knowledge.md` (audit-finding session note appended)

No Lean source changes.  No gallery `meta.json` changes.

## Honesty

This session **did not ship the intended docstring cleanup**.  It surfaced
that the file's "verified" claim is stale and propagating the cleanup would
have masked the real problem.  The net deliverable is a research audit
finding — modest value compared to ACT progress, but appropriate given the
finding's severity.
