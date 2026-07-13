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
by the backstop janitor (`scripts/clean-branches.sh` — currently missing from main,
see Known-Gaps Ledger) once clean and stale; dirty or unpushed worktrees are
always preserved.

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

## Known-Gaps Ledger (issue #38387)

Commit `dc9fdffa30` (PR #37576, merged 2026-07-11) accidentally deleted a large
portion of the engine from version control, including several helper scripts the
role prompts still reference. PR #38390 restored `scripts/research/`,
`scripts/auditor/`, `.loom/roles/`, and `.claude/agents/loom-*.md`. The following
are still referenced by role docs/prompts but **absent from `main`** — each is
recoverable verbatim from git history via `git show dc9fdffa30^:<path>`:

| Missing path | Referenced by | Notes |
|---|---|---|
| `scripts/deploy/sync-and-deploy.sh` | deployer | The chronic "deploy BLOCKED" cause |
| `scripts/deploy/launch-agent.sh` | deployer launch surface | |
| `scripts/herald/post-mathstodon.sh` | herald | Posting gate (rate limit, dedup, URL verify) |
| `scripts/herald/mastodon-client.ts` | herald | Replies/boosts/favourites |
| `scripts/herald/scan-engagement.ts` | herald | Hashtag engagement scan |
| `scripts/herald/launch-agent.sh` | herald launch surface | |
| `scripts/enricher/claim-target.sh` | enricher | Claim/complete tracker |
| `scripts/enricher/find-targets.ts` | enricher | Priority queue (passes/quality) |
| `scripts/enricher/parallel-enrich.sh` | enricher launch surface | |
| `scripts/auditor/launch-agent.sh` | auditor launch surface | |
| `scripts/mechanic/launch-agent.sh` | mechanic launch surface | |
| `scripts/agents/claude-wrapper.sh` | all launchers (incl. tracked `launch-seeker.sh`) | Daemon wrapper |
| `scripts/lean/update-stats.sh` | seeker | Stats/completion signals |
| `scripts/clean-branches.sh` | worktree janitor | |
| `scripts/gallery/check-meta-size.ts` | enricher | Size-guardrail check |
| `.claude/commands/lean-scout.md` | researcher (`/lean-scout` survey skill) | Structured literature/gallery survey |
| `.claude/skills/mathlib-contribution/` (SKILL.md, STYLE-SCAN.md, GOTCHAS.md) | researcher red-team pass for Mathlib-bound files | |
| `.lean/scripts/extract-problems.ts` | seeker | Pool extractor |
| `.lean/scripts/research.sh` | seeker, researcher | Workspace init; `phase` subcommand tracks OBSERVE/ORIENT/ACT/COMPLETED in `research/registry.json` |
| `.lean/scripts/knowledge-scores.sh` | researcher | Lists problems by knowledge score (`--status`, `--revisit`); `claim-problem.sh claim-random` covers the selection use case meanwhile |
| `.lean/scripts/archive-sessions.sh` | researcher | Archives old knowledge.md sessions to `sessions/`; manual archiving works meanwhile |
| `research/db/sync_pool.py`, `research/db/migrate.py` | seeker | DB-first pool sync (present only as untracked runtime state, currently absent from disk) |
| Root `package.json`, `vite.config.ts`, `tsconfig*.json`, `wrangler.toml` | `pnpm build` anywhere | Site builds currently only work in worktrees created from pre-deletion branches |

Do **not** reinvent these from scratch — restore from history (after a secrets
scan) or wait for the restoration decision, now tracked in follow-up issue
#38398 (#38387 covered the survey, engine check-in, role docs, and researcher-doc
optimization). Where a role doc references one of these paths, treat it as "the
documented behavior when the script is available".
