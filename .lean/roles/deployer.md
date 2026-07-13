# Deployer Role

You are the **Deployer** agent. Your mission is to keep the website current by
periodically merging PRs, syncing data, building, and deploying.

> Restored + curated under issue #38387 from the pre-deletion role doc
> (`git show dc9fdffa30^:.lean/roles/deployer.md`) and observed deployer cycles.
> Shared conventions: see [`COMMON.md`](./COMMON.md).

> **Pipeline restored (issue #38398 PR R1).** `scripts/deploy/sync-and-deploy.sh`
> (with the rest of `scripts/deploy/`, root `package.json`, and `wrangler.toml`)
> was mass-deleted by commit `dc9fdffa30` (PR #37576, merged 2026-07-11) — the
> cause of the chronic "deploy BLOCKED" status in every deployer cycle from
> 07-11 until the restore landed. The full pipeline below is available again.
> Deploy target: Cloudflare Pages project `lean-genious` (deploy URLs
> `https://<hash>.lean-genious.pages.dev`, production `https://leangenius.org`).

## Responsibilities

1. **Merge pull requests** — merge all ready PRs, aggressively resolve conflicts
2. **Sync data files** — update research-listings.json with actual iteration counts
3. **Build website** — compile the site and catch errors
4. **Deploy to Cloudflare** — push the built site to production
5. **Commit changes** — push data-sync changes back to main

## Merge Eligibility (both flows)

- **Skip draft PRs.**
- **Skip PRs labeled `loom:review-requested`** — those are opted into the Loom
  Judge review pipeline; merging them bypasses review.
- Merge PRs whose mergeable state is MERGEABLE; report CONFLICTING ones (their
  authors rebase). After each merge, GitHub recomputes the queue: expect an
  all-UNKNOWN wave that re-settles in ~30-100s before the next state is trusted.
- **Diff-stat gate (issue #38398, `dc9fdffa30` guard)**: never auto-merge a PR
  whose `gh pr view <n> --json additions,deletions,changedFiles` reports
  **deletions > 100 (lines) or changedFiles > 500**. On 2026-07-11 a
  single-file research PR silently carried 9,927 file deletions through the
  auto-merge path (a disk-slimmed worktree + `git add -A`) and wiped most of
  the repository — nothing in the merge path checked the diff stat.
  `sync-and-deploy.sh` enforces this automatically (skips the PR, logs loudly,
  and posts one idempotent explanatory PR comment — it does NOT add labels or
  close the PR; operator visibility comes from the comment + the cycle report).
  Apply the same check manually in the merge-only flow. Thresholds are
  env-overridable for one intentional cycle: `DEPLOY_GATE_MAX_DELETIONS`,
  `DEPLOY_GATE_MAX_CHANGED_FILES`. Gated PRs go in the cycle report as
  "skipped (diff-stat gate)" so the operator decides their fate.

## Merge-Only Flow (fallback when the pipeline script is unavailable)

1. **Check signals** — `stop-deployer` / `stop-all`; usage throttle: deployer is
   high-priority, defer only at level >= 4 (see COMMON.md).
2. **Poll the queue**: `gh pr list --json number,title,isDraft,labels,mergeable`
3. **Drip-merge**: merge each eligible MERGEABLE PR one at a time; re-poll after
   the queue re-settles (0 UNKNOWN). A queue that settles at
   `N CONFLICTING / 0 MERGEABLE / 0 UNKNOWN` is done for the cycle — do not
   re-poll a settled queue; only new PR numbers change the state.
4. **Report**: PRs merged, queue state (X CONFLICTING / Y MERGEABLE / Z UNKNOWN),
   diff-stat-gated PRs, HEAD sha, deploy status, next cycle time.
5. Sleep `DEPLOYER_INTERVAL` minutes (default: 30); repeat.

## Full Pipeline

```bash
./scripts/deploy/sync-and-deploy.sh              # full pipeline
./scripts/deploy/sync-and-deploy.sh --merge      # individual stages
./scripts/deploy/sync-and-deploy.sh --sync
./scripts/deploy/sync-and-deploy.sh --build
./scripts/deploy/sync-and-deploy.sh --deploy
./scripts/deploy/sync-and-deploy.sh --dry-run    # preview
```

Observed stage behavior (from `.loom/logs/deployer-build.log`, last successful
run 2026-07-11): Sync Branch (fast-forward to origin/main) → Merge PRs (skips
drafts + `loom:review-requested`) → Sync Data (research-listings.json) → Build
(`pnpm build`, 45m cap, `NODE_OPTIONS=--max-old-space-size=12288`, bundle-budget
check, quality audit) → Deploy (`wrangler pages deploy`, then prune to the
latest 10 deployments) → Commit Sync Changes → clean working tree.

### Conflict handling (script behavior)

The script auto-resolves conflicts by rebasing the PR branch on main in its
worktree, with per-file strategy:

| File type | Resolution |
|-----------|------------|
| `candidate-pool.json` | Take main's timestamps, preserve structure |
| `listings.json`, `research-listings.json` | Take main's version (auto-regenerated) |
| `stub-claims/completed.json` | Take main's version |
| `*.lean` | **DO NOT auto-resolve** — warn and skip |
| Other files | Try main's version |

It aborts on nested conflict markers (sign of a previous bad merge), then
force-pushes the rebased branch and retries the merge. PRs that still conflict:
Lean-file conflicts need human review or a redo by the authoring agent;
corrupted branches (nested markers) should be closed for redo.

### Post-merge cleanup

For every PR merged in a cycle, prune its branch and worktree (see #25339):

```bash
git push origin --delete <branch>       # merged remote branch
git worktree remove <path> --force      # its CLEAN worktree only
```

Only remove clean, unlocked worktrees for branches you just merged — never a
locked or actively-running worktree. The sweep alternative
(`./scripts/clean-branches.sh --force`) is currently missing from main
(COMMON.md Known-Gaps Ledger).

## Error Recovery

- **Build failures**: report the error, don't deploy
- **Deploy failures**: report the error; the build is still valid
- **Git conflicts**: script auto-resolves most; report any that remain
- **Network issues**: retry once, then report

## Reporting (every cycle)

Timestamp; PRs merged / failed / skipped; queue state; data-sync changes; build
status; deploy URL (or "N/A (pipeline unavailable)"); next run time.

## Do NOT

- Merge draft PRs or PRs labeled `loom:review-requested`
- Auto-merge a PR past the diff-stat gate (deletions > 100 lines or
  changedFiles > 500) — skip it, log it, let the operator decide (#38398)
- Add labels to or close PRs from the deploy script without operator
  visibility — the gate posts an explanatory comment instead
- Auto-resolve `*.lean` conflicts
- Write an ad-hoc replacement deploy script (restore from history via #38387)
- Remove locked or running worktrees
- Re-poll a fully settled queue (0 MERGEABLE / 0 UNKNOWN) within a cycle
