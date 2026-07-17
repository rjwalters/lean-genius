# Mathlib/Toolchain Migration Toolkit

Reusable machinery for migrating the whole `proofs/Proofs/*.lean` gallery across a
Lean-toolchain + Mathlib version bump (e.g. v4.26.0 → v4.31.0, epic #37508). Built and
proven on the v4.26→v4.31 migration, which took the residual failure set from ~570 files
to near-zero via a parallel single-proof-per-agent fleet. Save this — the next bump reuses
it directly; only the version strings and the seam catalog change.

## The model: one proof file per agent, many agents in parallel

NOT "one issue per agent" and NOT batching many files into one agent. Each subagent owns
**exactly one** `.lean` file, edits only that file, verifies it compiles in Docker, and pushes
a per-proof branch `mig/<File>`. An orchestrator (the main loop) collects each green, re-verifies
it in a clean container, flips one ledger row, and merges. This gives:

- **Isolation**: an agent that fails/stalls/OOMs affects one file, not a batch.
- **Trivial merges**: row-level ledger flips never conflict (see `collect.sh`).
- **A ground-truth ledger** (`proofs/batch2/verify-results.tsv`, columns `<BareModuleName>\tSTATUS\tclass`)
  that is the single source of truth for what's GREEN / RESIDUAL / PRE-EXISTING.

### Why "the theorem is TRUE, only the spelling changed" framing matters
Every RESIDUAL file was GREEN on the old toolchain, so a proof existed and the statement is
true — the bump only changed *how it's spelled* (renames, signature changes, tactic-behavior
shifts). So each file is EXPENSIVE (many drift sites) but never "impossible." Agents grind, they
don't give up. The three real exceptions are enumerated in the agent prompt: unsound-originals
(fix to the genuinely-true form, log to the soundness issue), deep-rework, and OOM.

## Files in this toolkit

| File | Purpose |
|------|---------|
| `single-proof-prompt.template.md` | The agent playbook. Substitute `{{FILE}}`/`{{WORKTREE}}`/`{{CACHE_VOL}}`/`{{CPUSET}}`/`{{VER}}` per dispatch. Contains the verify recipe, the FRAMING, the finish protocol, the native_decide axiom-integrity rule, and a seam cheatsheet. |
| `collect.sh` | The **conflict-proof collector**. For each pushed `mig/<file>`, applies ONLY its `.lean` + flips its single ledger row AFTER re-verifying EXIT=0 in a clean container. Never `git merge`s a mig branch. This is the safety gate that catches false-greens and case-collisions. Env-driven (see header). |
| `SLOT-TABLE.template.txt` | Canonical slot→worktree→cache-volume→cpuset mapping. NEVER dispatch two agents to one worktree/cache concurrently. |
| `38611-statement-repairs-*.txt` | Log of every genuine soundness/statement repair surfaced by the stricter new toolchain (false theorems that old tactics accepted). Deliverable for the gallery re-audit issue. |
| `38612-deep-rework-defers-*.txt` | Files too broken for a single migration pass (3000+-line WIP scaffolds, sorry-tainted native_decide, unsound-originals needing new math). Deliverable for the deep-rework issue. |

## Orchestrator loop (main-loop responsibilities)

1. **Build the queue** from the ledger: `awk -F'\t' '$2=="RESIDUAL"{...print bare module name}'`.
   The queue must equal exactly `RESIDUAL − in-flight − deep-rework-defers`. Reconcile it against
   the ledger periodically — it drifts (orphans appear).
2. **Dispatch** one file per free slot per `SLOT-TABLE`, substituting into the agent prompt.
   Front-load base `*Problem` files ahead of their `*Aristotle`/`*OQ*` companions (children `import`
   parents; fixing a parent first turns the child into a cheap cascade).
3. **Collect** each pushed green via `collect.sh` (re-verify → flip row → merge). One PR per batch.
4. **Refeed** each freed slot from the queue **in the same turn you reset it** (else slots idle).
5. **Audit every ~10 batches**: dead slot = `idle-*` branch + no container + no recent `.lean` mtime +
   branch not in recent `origin/mig/*` pushes → reset + re-dispatch. ~2 silent setup deaths/hour.
6. **Sequence cascades across waves, never concurrently across slots**: a child dispatched while its
   parent is still in flight fails "blocked by dependency" and wastes an agent.

## Hard-won gotchas (all cost real time — read before reusing)

- **Ledger col1 is the BARE module name** (`Erdos395OQ01`), NOT a path and NOT `.lean`-suffixed. A
  row-flip that matches on `.lean` silently fails; the GREEN count then rises by fewer than you merged.
- **NEVER `git checkout <mig-branch> -- verify-results.tsv`** (whole-file). Mig branches are cut from an
  older base; their tsv is STALE and clobbers every row-flip merged since. Only ROW-LEVEL flips.
- **Case-insensitive filesystem collisions** (macOS): `Foo.lean` and `foo.lean` are two git-tracked paths
  that collapse to one inode; `git add` updates only one, leaving the other stale → false-green on reverify.
  Fix both entries with `git update-index --cacheinfo`.
- **Cascade artifact**: a lone "object file `<Parent>.olean` does not exist" means a GREEN parent isn't in
  the slot's cache volume — `lake build Proofs.<Parent>` (NOT `lake env lean`, which doesn't write oleans)
  into the cache first, then the child usually compiles with no edits.
- **The collector's clean-container re-verify is non-negotiable** — it repeatedly caught false-greens
  (partial fixes an agent claimed but that didn't actually hold) before they could merge.
- Never dispatch two agents to one worktree/cache (branch tangles → false-green non-compiling merges).

## Model choice (CORRECTED 2026-07-16 — Fable is the escalation, not Opus)

Default **every** slot to Sonnet — across ~90 hard files PLUS the entire #38612 deep-rework tail it had
almost zero genuine capability failures (it cleared 300k+ constructibility towers, 198k/290k/450k Sylow &
Sperner & Turan deep-reworks, and the native_decide/noncomputable-`SetLike.instFintype` blocker — with a
reusable explicit-subgroup + brute-force-normalizer + Lagrange workaround). Escalate to **Fable**
(`model: 'fable'`) — NOT Opus — on a genuine Sonnet capability-FAIL (Sonnet edited+verified and still
couldn't close it; a dependency block is NOT a capability fail — sequence the parent instead). Fable is
significantly MORE powerful and more expensive than Sonnet: it is the top tier here and the escalation
target (proven on deep-rework — it fixed Erdos60Problem and caught a #38611 soundness bug an ∀n conjecture
false at n=4). Because Fable is pricier, escalate deliberately, one file at a time — not as a bulk default.
Do NOT use Opus (wrong tier here) or Haiku (thrashes). Availability caveat: Fable can hit sustained
`529 Overloaded` windows (capacity, not capability — one such window on 2026-07-16 killed ~11 launches
before any Lean ran); back off ~20 min and retry rather than hammering idle slots.


## Infra (this host)
- Docker relocated to `/Volumes/Stripe/docker` (sparse `Docker.raw` via symlink); VM memory raised to 47 GB.
  `--memory` cap (not host RAM) bounds concurrency; a single-file `lake env lean` uses ~4–6 GB, so ~7–8 fit.
- Named cache volumes `lean-mathlib-cache-v431[/-b/-c/…]` (one per slot to avoid lock contention) +
  a shared read-mostly `lean-mathlib-packages-v431`. Build image `lean4-arm64:v4.31.0`.
- Worktrees on the 3.6 TiB `/Volumes/Stripe` (`.loom/config.json` `worktree.root`), NOT the boot disk.

## For the NEXT bump (checklist)
1. Bump `VER` everywhere (`v431`→new), rebuild the Docker image + seed per-slot cache volumes.
2. Run the full gallery once on the new toolchain to produce the RESIDUAL ledger (the failure set).
3. Copy `single-proof-prompt.template.md` → substitute the new version; START the seam cheatsheet fresh
   (drift is version-specific) but keep the *structure* and the behavior-class list (they recur).
4. Reuse `collect.sh` and `SLOT-TABLE` verbatim (env-driven).
5. Open the two follow-up issues (soundness re-audit, deep-rework) and attach the accumulating logs.
