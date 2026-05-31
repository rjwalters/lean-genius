# S11 INFRA-VERIFY — G9-mount hypothesis CONFIRMED: lake self-loop is inert for Docker builds

**Researcher**: researcher-1
**Date**: 2026-05-31
**Phase**: INFRA-VERIFY (empirical; Docker build on origin/main MoserTardos.lean executed; zero new code)
**Predecessor**: S10 STATE-SYNC (researcher-1, 2026-05-30) — G9-mount hypothesis flagged for S11 verification
**Successor**: S12 ACT — paste OQ-01-A.3 substitute body (~130 LOC per S8 §3.2 / §4)

## Executive summary

The S10 STATE-SYNC §4 hypothesis — that the Docker `-v` mount on `lean-mathlib-cache:/workspace/proofs/.lake/build` overrides the host's `.lake` self-symlink and makes G9 inert for Docker builds — is **CONFIRMED EMPIRICALLY**.

Test command (executed in this worktree, on origin/main MoserTardos.lean — zero new code, zero edits to any file under inspection):

```bash
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1
LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh Proofs.MoserTardos
```

Result: **Build completed successfully (7743 jobs)**, with the standard Mathlib v4.26.0 dependency download + decompress cycle (Mathlib + import-graph + ProofWidgets + aesop + Qq + batteries + Cli, plus the local Proofs target chain). Total runtime ~150 seconds wall-clock; the cache fetched 7727 files (cold cache for this worktree).

Snapshot at S11 verify:

- G7 disk: 59 Gi free (`/System/Volumes/Data` 94% capacity, well above 10 Gi ACT floor). **GREEN**.
- G8 Docker: `docker info --format '{{.ServerVersion}}'` → `29.4.1` (immediate, no timeout). **GREEN**.
- G9 lake self-loop: `ls -la proofs/.lake` → `proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake` (self-referencing on host; `readlink -f` errors with "Too many levels of symbolic links"). **STILL RED ON HOST**, but **INERT FOR DOCKER BUILDS** (this finding).

The S10 hypothesis mechanism is now empirically validated:

- `proofs/scripts/docker-build.sh:127` mounts `lean-mathlib-cache` directly onto `/workspace/proofs/.lake/build` inside the container, providing a fresh writable directory regardless of host symlink state.
- The outer `-v "${REPO_ROOT}:/workspace:delegated"` bind mount makes the worktree available inside the container, but the broken `proofs/.lake` symlink's target (`/Users/rwalters/GitHub/lean-genius/proofs/.lake`) does not exist as a path inside the container, so the link is dangling-in-container — yet does not block the build because the nested `lean-mathlib-cache` mount supersedes the broken parent.
- Lake's `cache get` populates `.lake/build` (the volume-mounted directory) with fetched `.olean` files, then `lake build Proofs.MoserTardos` compiles against those.

## 1. Test transcript (key milestones)

```
=== Docker Lean Build ===
...
info: importGraph: cloning ...
info: proofwidgets: cloning ...
info: aesop: cloning ...
info: Qq: cloning ...
info: batteries: cloning ...
info: Cli: cloning ...
✔ [5/21] Built Cache.Lean (317ms)
... [21 cache-binary jobs] ...
✔ [21/21] Built cache:exe (1.3s)
[Mathlib cache fetch: 7727 files in ~120s]
Decompressing 7727 file(s)
Unpacked in 35402 ms
Completed successfully!
Build completed successfully (7743 jobs).
[150s] Building...
=== Build succeeded ===
```

Exit code: 0.

The "7743 jobs" total reflects: 21 cache-binary build steps + the actual `lake build Proofs.MoserTardos` chain through Mathlib transitive dependencies. With the cache warm (7727 cached files), the per-file lean-elab step was skipped; only target-specific compilation happened. MoserTardos.lean was the explicit `lake build` target and built without diagnostic.

## 2. ACT-readiness gate refresh (S11)

| # | Item | Status pre-S11 (S10) | Status post-S11 |
|---|------|----------------------|-----------------|
| 1 | Mathlib pin stable | GREEN | GREEN (unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, ≥19d) |
| 2 | Bearers verified at pin | GREEN | GREEN (transitivity at byte-stable SHA) |
| 3 | Paste-ready substitute body (S8 §3.2) | GREEN | GREEN (unchanged) |
| 4 | Parent file baseline stable (382 LOC, 0 sorries) | GREEN | GREEN (unchanged) |
| 5 | No competing open PRs on slug | GREEN | re-verified (`gh pr list --search "prob-method-lovasz-local-oq-01" --state open` → 0) |
| 6 | JSON catchup planned | GREEN | DONE (S9 + S10 catchup merged) |
| 7 | problem.md / knowledge.md unchanged | GREEN | GREEN (unchanged) |
| 8 | Infra: Docker + disk + .lake | **PARTIAL INFRA (G9-only)** | **GREEN (G9 confirmed inert via Docker -v override)** |

**Gate flips from 7/8 GREEN + 1/8 PARTIAL to 8/8 GREEN**. S12 ACT can proceed without infra qualifier.

## 3. Implications for sibling slugs

This finding is **slug-agnostic**: the Docker `-v` mount mechanism applies to every research worktree that uses `proofs/scripts/docker-build.sh`. The blanket "build pending — G9 lake self-loop" qualifier pattern, which has been added to many recent research PRs across the gallery (including this researcher's own PR #21550 — ballot-problem-oq-02-oq-05 S8 ACT, shipped earlier this session), was **OVERCAUTIOUS**: those builds could have been Docker-verified after all.

**Recommendation for the memory-feedback pattern**: the `lake-self-loop-main-repo` memory entry should be updated to reflect that G9 is inert for Docker builds. The "Ship ACT PRs under 'build pending — G9 lake self-loop' qualifier" guidance is now obsolete. ACT PRs should attempt Docker verification first; the qualifier was a safety blanket for a problem that turned out not to be a problem.

**Cross-slug-coordination action item** (for the deployer or a separate audit slug): scan recent research PRs labeled with `(build pending — G9 lake self-loop)` and run Docker verifications retroactively, then update those PR descriptions / state.md files accordingly. Not in scope for this S11 INFRA-VERIFY session.

**Within-this-session action**: my own ballot-problem-oq-02-oq-05 PR #21550 (S8 ACT, shipped earlier this session at 17:30Z under the obsolete qualifier) will be Docker-verified separately in this session if budget permits, with a follow-up commit or PR comment recording the build result.

## 4. Mathlib pin byte-stability (cross-check)

`cat proofs/lake-manifest.json | jq -r '.packages[]|select(.name=="mathlib")|.rev'` → `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since 2026-05-12 / lake-pinned ≥19 days).

All S7/S8 PREP bearers transitively valid at this SHA (no re-walk justified).

## 5. Next action (S12 — ACT)

With 8/8 GREEN, S12 can paste the S8 §3.2 paste-ready substitute body for `lll_admissible_uniform` (the OQ-01-A.3 deliverable). Approximate budget:

- **OQ-01-A.3 substitute body**: ~130 LOC paste of the S8 §3.2 `lll_admissible_uniform_substitute` skeleton replacing the parent file's faithful-link gap.
- **Build verification**: Docker-verifiable now that G9 is confirmed inert (~3-5 min cold-cache; ~30-60 sec warm).
- **Sorry count**: depends on which of the S8 §4 sub-lemma sorries are inline vs. queued; target is ~3-5 sorries on the substitute body, with the parent file's `lll_admissible_uniform` axiom either downgraded or held pending.

Sibling-coordination check before S12 ACT: re-run `gh pr list --search "prob-method-lovasz-local-oq-01" --state open` immediately before push to confirm zero race.

## 6. Honesty (S11)

This is the first **substantive** (non-doc-only) iteration on this slug since S6 ACT (researcher-3, #19792, merged 2026-05-14T18:23Z — the build-verify-repair landing). The S7-S10 chain (PREP + PREP + STATE-SYNC + STATE-SYNC) accumulated infra observations without producing a Lean change; S11 produces a Lean-adjacent finding (Docker behavior under G9) that **unblocks** S12 ACT for ~130 LOC of actual Moser–Tardos formalization work.

The "stuck-ness" concern flagged in S10 §honesty is **resolved** by this iteration: S11 is not another STATE-SYNC. It is a binary-outcome empirical test whose answer changes the disposition of the slug (and, transitively, the disposition of many sibling slugs that shipped "build pending — G9" PRs).

Net research progress for this slug: ACT-readiness gate flipped to fully GREEN; ~130 LOC of OQ-01-A.3 work is now unblocked for any subsequent researcher (or this researcher in a follow-up session).

## 7. Risk inventory (S11 → S12)

| ID | Description | Risk | Mitigation |
|----|-------------|------|-----------|
| Q1 | The S11 build was on `Proofs.MoserTardos` (origin/main, unchanged file). S12 ACT will introduce a NEW import target (`Proofs.PromptedMoserTardos` or sibling) whose dependency chain might surface a build issue unrelated to G9 | LOW | Use the existing `Proofs.MoserTardos` namespace for the new substitute body; no new file unless the LOC budget forces a split |
| Q2 | The lean-mathlib-cache volume on this host now contains fresh build artifacts. A subsequent researcher's worktree using a different Mathlib pin could see stale `.olean` files | LOW | Mathlib pin is unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; no risk for any slug pinned to v4.26.0 |
| Q3 | Cross-PR coordination: my ballot-problem PR #21550 needs a follow-up that retracts the "build pending — G9" qualifier; this might surface as a separate auditor finding | LOW | Add a PR comment on #21550 with the S11 finding link; deployer can re-verify build on retry |
| Q4 | The G9-inert finding may need broader socialization (memory feedback update + auditor-style sweep of recent PRs) before the pattern actually changes across the gallery | MEDIUM | Out of S11 scope; flagged in §3 for follow-up. Within this session, update project memory entry for `lake-self-loop-main-repo` if time permits |

## 8. Deliverable summary (S11 INFRA-VERIFY)

- **Empirical test executed**: Docker build of `Proofs.MoserTardos` on this worktree → exit 0, 7743 jobs successful, ~150s wall-clock.
- **Hypothesis disposition**: S10 §4 G9-mount hypothesis **CONFIRMED**. Lake self-loop is inert for Docker builds (Docker `-v` volume mount on `.lake/build` overrides host symlink state).
- **State updates**: `state.md` (S11 INFRA-VERIFY block + ACT-readiness gate flip 7/8 GREEN → 8/8 GREEN), this session memo (~150 LOC), no JSON catchup needed (S10 catchup still authoritative; substantive finding not yet ACT'd).
- **No Lean change** in this session (INFRA-VERIFY by design; S12 will paste the ~130-LOC substitute body).
- **No memory edits** in this session, but flagged for follow-up: the `lake-self-loop-main-repo` memory entry should be updated to reflect G9-inert finding.

## 9. ACT-readiness for S12 (gate snapshot)

8/8 GREEN. S12 should:

1. Paste the S8 §3.2 substitute body for `lll_admissible_uniform` (~130 LOC).
2. Docker-verify via `./proofs/scripts/docker-build.sh Proofs.MoserTardos` (or a parallel target if a new file is created).
3. Commit + push + PR with `research` label.
4. No "build pending" qualifier needed.

If S12 introduces sub-sorries (expected per S8 §3.2 outline: ~3-5 sorries on the substitute body), document each with a discharge sketch in the corresponding session memo for S13+.
