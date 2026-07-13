# Fleet Common Conventions

Shared conventions for all lean-genius fleet agents (researcher, seeker, enricher,
auditor, deployer, herald, mechanic). Role docs reference this file instead of
repeating these sections. Role-specific deltas (different signal names, different
throttle thresholds) live in each role doc.

## Signals

Every agent checks for signal files under `$REPO_ROOT/.loom/signals/` **before
starting each iteration**:

```bash
# Stop: exit gracefully. <role> is your role/agent id (e.g. seeker, enricher-1).
if [[ -f "$REPO_ROOT/.loom/signals/stop-<role>" ]] || \
   [[ -f "$REPO_ROOT/.loom/signals/stop-all" ]]; then
    echo "Stop signal received. Exiting."
    exit 0
fi

# Pause: wait until a continue signal appears, then consume it.
while [[ -f "$REPO_ROOT/.loom/signals/pause-all" ]] || \
      [[ -f "$REPO_ROOT/.loom/signals/pause-<role>" ]]; do
    echo "Paused. Waiting for continue signal..."
    sleep 30
    if [[ -f "$REPO_ROOT/.loom/signals/continue-all" ]] || \
       [[ -f "$REPO_ROOT/.loom/signals/continue-<role>" ]]; then
        rm -f "$REPO_ROOT/.loom/signals/continue-all" \
              "$REPO_ROOT/.loom/signals/continue-<role>"
        break
    fi
done
```

## Rate Limits and Usage Throttling

If you hit an API rate limit, **do not exit** — enter pause state so you can
finish current work and shut down gracefully:

```bash
touch "$REPO_ROOT/.loom/signals/pause-<role>"
# then fall into the pause loop above
```

Session usage throttling (where the check script is available):

```bash
throttle=$("$REPO_ROOT/.loom/scripts/check-usage.sh" --throttle 2>/dev/null || echo "4")
```

- Most agents pause/exit at throttle level **>= 3** (high usage).
- The deployer has higher priority and only defers at level **>= 4** (critical).

> `.loom/scripts/check-usage.sh` is runtime infrastructure that is not currently
> version-controlled (see Known-Gaps Ledger below). The `|| echo "4"` fallback
> means a missing script reads as "critical", which fails safe.

## Observability (Actions Log)

Log significant actions — one brief line each — so the fleet can be monitored
without TUI access:

```bash
echo "$(date +%H:%M): ACTION_DESCRIPTION" >> "$REPO_ROOT/.loom/logs/<agent-id>.actions.log"
```

Examples: `Claimed weak-goldbach`, `Created PR #456, releasing claim`,
`SKIP pythagorean-theorem (over size cap)`.

Long-form per-cycle output goes to the wrapper-managed log
(`$REPO_ROOT/.loom/logs/<agent-id>.log`); the actions log is the terse audit trail.

## Worktree Hygiene

Worktree-based agents (researcher, enricher, seeker) work in the **sanctioned
location** `$REPO_ROOT/.loom/worktrees/<agent-id>` on branch `feature/<agent-id>`.
Do not create defensive worktrees under `$HOME` or `/tmp` — the create path
preserves in-flight work. Stray worktrees outside `.loom/worktrees/` are reclaimed
by the backstop janitor (`scripts/clean-branches.sh`) once clean and stale;
dirty or unpushed worktrees are
always preserved.

**NEVER delete tracked files from disk to reclaim space.** Git sees raw disk
deletions as pending changes, and a later stage-all commit (`git add -A`) will
faithfully stage them as deletions — this is exactly how commit `dc9fdffa30`
mass-deleted 9,927 files from main (issue #38398). If a worktree must be slimmed
under disk pressure, use the sparse-checkout helper, which removes files from
disk while marking them skip-worktree so git does NOT see them as deleted:

```bash
# Slim: keep only the listed directories (cone mode)
scripts/research/slim-worktree.sh --worktree <path> proofs research/problems/<problem>
# Undo: restore the full checkout
scripts/research/slim-worktree.sh --worktree <path> --restore
```

Related guards (all from #38398): researcher worktrees get a `pre-commit`
mass-deletion tripwire (`scripts/research/check-staged-deletions.sh` — more
than 20 staged deletions blocks the commit; `ALLOW_MASS_DELETION=1` bypasses),
`parallel-research.sh` refuses to launch a researcher into a worktree with >5%
of tracked files missing on disk and sparse-checkout off (`LAUNCH_ANYWAY=1`
overrides), and the deployer skips auto-merging PRs with >100 deleted lines or
>500 changed files (see `deployer.md`).

## Honesty Standards

- Do not describe trivial results as significant.
- Do not inflate novelty claims — if the result is routine, say so.
- If nothing worth doing/reporting exists, say "nothing found" rather than
  fabricating value. A cycle that correctly stands down is a successful cycle.
- Judge results relative to current gallery state, not in absolute terms.
- A lemma that filled a gap 3 months ago may be trivial now if stronger
  results exist.
- When uncertain about significance, default to understating rather than
  overstating.

## Known-Gaps Ledger (issue #38387 / #38398)

Commit `dc9fdffa30` (PR #37576, merged 2026-07-11) accidentally deleted ~9,900
files from version control. Restoration history: PR #38390 restored
`scripts/research/`, `scripts/auditor/`, `.loom/roles/`, and
`.claude/agents/loom-*.md`; PR #38392 the six role docs; #38398 PR R1 restored
the remaining root + engine files (root `package.json`/`vite.config.ts`/
`tsconfig*`/`wrangler.toml`/`Makefile`/`CLAUDE.md`/`README.md`, `scripts/deploy/`,
`scripts/herald/`, `scripts/enricher/`, `scripts/agents/claude-wrapper.sh`,
`scripts/lean/update-stats.sh`, `scripts/clean-branches.sh`,
`scripts/gallery/check-meta-size.ts`, `scripts/annotations/`, `.lean/scripts/`,
`.claude/commands/`, `.claude/skills/mathlib-contribution/`, `functions/`,
`drizzle/`, `mcp-servers/aristotle/`, and more); #38398 PR R2 restored
`research/problems/`; #38398 PR R3 added the four recurrence guards (commit
tripwire, deployer diff-stat gate, sparse-checkout slimming helper, worktree
health check — see Worktree Hygiene above and `deployer.md`).

Remaining gaps (deliberately NOT restored):

| Missing path | Referenced by | Notes |
|---|---|---|
| `research/db/sync_pool.py`, `research/db/migrate.py` | seeker | `research/db/` is gitignored (runtime state); currently absent from disk too — restoration/tracking decision deferred to the operator (#38398 item 3) |
| `research/registry.json` tracking decision | researcher, seeker | Fleet-mutated: conflict risk; deferred by the operator in #38387 |
| `research/db/knowledge.db` dump strategy | researcher | Binary SQLite — not git-friendly; deferred |

Do **not** reinvent missing paths from scratch — restore from history (after a
secrets scan; everything is recoverable verbatim via `git show
dc9fdffa30^:<path>`). Where a role doc references a still-missing path, treat it
as "the documented behavior when the script is available".
