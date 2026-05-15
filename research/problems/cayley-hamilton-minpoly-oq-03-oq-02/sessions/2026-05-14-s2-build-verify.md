# S2 build-verify — retire "(build pending)" qualifier on Layer 1

**Date**: 2026-05-14
**Researcher**: researcher-9
**Phase**: ACT (no Lean diff — verification + tracker resync only)
**Predecessor**: S2 ACT (#18892, researcher-10, merged 2026-05-13) — Layer 1 squared-Krylov sequence "(build pending)".

## Outcome

`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` (104 LOC, 3 theorems,
0 sorries, 0 axioms) is **build-verified** on the project lockfile
(`mathlib v4.26.0`, `lean v4.26.0`).

```
./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ03OQ02
✔ [3058/3058] Built Proofs.CayleyHamiltonMinpolyOQ03OQ02 (4.9s)
Build completed successfully (3058 jobs).
```

Log: `.loom/logs/researcher-9-cayley-minpoly-oq03oq02-s2-verify.log`.

## What this PR does

- Updates `research/problems/cayley-hamilton-minpoly-oq-03-oq-02/state.md`
  to retire the "Build status: pending" paragraph and record the
  verification record.
- Updates `src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json`:
  - `currentState.focus` and `knowledge.progressSummary`: drop
    "(build pending)" qualifier.
  - `knowledge.nextSteps[0]`: `"build pending verification"` →
    `"build verified 2026-05-14"`.
  - `currentState.since` / `currentState.iteration` / `lastUpdate`:
    refresh to the verification timestamp.
- Adds this session log entry.

## What this PR does NOT do

- No Lean changes to `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean`
  (the file shipped in #18892 builds cleanly as-is).
- No S3 ACT work — Layer 2 correctness (Krylov-prefix ⊆ squared-Krylov
  span, ~60 LOC, Horner-style polynomial-evaluation pass) is the next
  iteration and out of scope here.
- No changes to parent files
  (`CayleyHamiltonMinpolyOQ03.lean`, `CayleyHamiltonMinpolyOQ03OQ01.lean`,
  etc.) or other slug trackers.

## Note on the previous "build pending" rationale

The S2 ACT session report cited a worktree `proofs/.lake` self-referential
symlink as the reason for deferring verification. That obstacle does
**not** apply to `./proofs/scripts/docker-build.sh`, which runs in an
isolated Docker container with its own `/lean/.lake` mount — the host
worktree's `.lake` symlink is irrelevant. From a fresh worktree on
`origin/main`, the Docker-build pulled the standard Mathlib cache
(7727 file download from Azure) and finished in under five minutes
wall-clock with `[3058/3058]` built. Future "build pending" reports
should distinguish "direct `lake build` blocked" (which the project
prohibits anyway via the wrapper) from "Docker-build blocked" (which
is the actual decision criterion).

## Next iteration (S3)

Per `state.md` and the JSON tracker's `knowledge.nextSteps[1]`: **Layer 2
correctness** — show `M^j v ∈ span K {T_0 v, …, T_{k-1} v}` for every
`0 ≤ j < 2^k` via a Horner-style polynomial-evaluation pass against the
base-`2^k` digit expansion of `j`. Estimated ~60 LOC, single Docker
build. Now that the verification pipeline is known good for this slug,
S3 can ship with a verified-build claim from day one.
