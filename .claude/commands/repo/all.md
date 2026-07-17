---
name: "all"
description: "The whole hygiene pass in order — audit, tidy, update-tools, reset — each report-first"
domain: repo
type: command
user-invocable: true
---

# /repo:all — The Whole Hygiene Pass

Run the full sequence of sensible repo work in one go: scan for problems, tidy
filesystem clutter, refresh installed tool packages, and land back on a clean
baseline. This is the umbrella command — it orchestrates the other `/repo:*`
commands in a deliberate order, but changes nothing without the same
report-first confirmation each of them uses on its own.

It deliberately does **not** launch cloud dev sessions ([[remote]]) — that
provisions paid infrastructure and is never part of a routine hygiene pass.

## Usage

```
/repo:all                      # Full repo, every stage, interactive
/repo:all packages/core        # Scope the read-only scans to one subtree
/repo:all --prune              # Auto-delete confirmed-safe branches/worktrees (passed to reset)
```

The optional path argument scopes the scanning stages ([[audit]]) the same way
it does for those commands. Stages that act on global git or filesystem state
([[tidy]], [[reset]]) always operate on the whole repo.

## Stages

Run these in order. **Between each stage, show what was found and get a yes
before acting** — do not chain destructive steps silently. If the user declines
a stage, note it and continue to the next.

### 1. Audit (see [[audit]])

Run the full read-only health sweep: README accuracy, orphaned files, broken
links, gitignore issues, branch & worktree hygiene. Produce the combined audit
report. This surfaces everything before anything is touched.

Offer to fix the fixable findings (stale READMEs, broken links, gitignore
rules) here, since the next stages won't.

### 2. Tidy (see [[tidy]])

Inventory filesystem clutter — build artifacts, caches, temp files, empty dirs
— present it grouped with sizes, and remove what the user approves.

### 3. Update tools (see [[update-tools]])

Check installed tool packages (Loom, Anvil, Repo itself, …) against their
sources. Report what's behind and offer to update.

### 4. Reset (see [[reset]])

Last, because it changes branch state and syncs with the remote. Run the
end-of-task baseline ritual: working-tree safety check, stash review, branch &
worktree pruning, `git fetch --prune`, and return to the default branch. Pass
`--prune` through if it was given to `/repo:all`.

Do this stage last so the earlier scans and cleanup happen while you're still on
the working branch, and you finish on a clean default branch.

## Final Summary

After all stages, print one consolidated report so nothing is silently
forgotten:

```
REPO:ALL COMPLETE
=================
Audit:        3 findings (2 fixed, 1 deferred: docs/analysis/ missing README)
Tidy:         freed 240 MB (build/, .cache/, 3 empty dirs)
Tools:        Anvil updated 1.4.0 → 1.5.1; Loom current
Reset:        on main (up to date), tree clean, 4 branches deleted, 1 stash kept
Skipped:      remote (never part of /repo:all)
```

List anything intentionally left behind — deferred findings, kept stashes,
UNKNOWN branches — so the user knows exactly what state the repo is in.

## Principles

Same as every hygiene command: **report first, fix second**; **general by
design**; **don't be noisy**. `/repo:all` adds only sequencing — each stage
keeps its own confirmation step, and no stage is skipped or auto-approved just
because it runs under the umbrella.
