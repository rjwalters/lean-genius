---
name: "branches"
description: "Audit local branches and worktrees — find merged PRs, orphaned worktree branches, and stale worktrees"
domain: repo
type: command
user-invocable: true
---

# /repo:branches — Branch & Worktree Hygiene

Find stale local branches and worktrees that can be safely removed. Reports
findings and waits for confirmation before deleting anything.

## Usage

```
/repo:branches                   # Full audit
/repo:branches --prune           # Delete confirmed-safe branches after reporting
```

## Steps

### 1. Inventory

Gather current state:

```bash
# Default branch
git symbolic-ref --short refs/remotes/origin/HEAD 2>/dev/null | sed 's|origin/||'

# Count local branches
git branch --list | wc -l

# List worktrees
git worktree list

# Identify active worktree branches (these are PROTECTED)
git worktree list --porcelain | grep '^branch ' | sed 's|branch refs/heads/||'
```

### 2. Categorize branches

For every local branch, classify it into one of these buckets:

#### PROTECTED (never delete)
- The default branch (`main`/`master`) and the currently checked-out branch
- Any branch currently checked out by a worktree
- Any branch with an **open** PR (`gh pr list --head <branch> --state open`)
- Long-lived branches the repo's own docs (CLAUDE.md, CONTRIBUTING.md) name as
  release/project branches — if such a list exists, honor it

#### MERGED PR BRANCHES
- Branches matching common PR patterns: `feature/*`, `fix/*`, `feat/*`, `pr-*`
- Check if a PR exists and is merged:
  `gh pr list --head <branch> --state merged --json number --jq length`
- If the PR is merged, the branch is safe to delete
- Also safe: any branch fully merged into the default branch
  (`git branch --merged <default>`)

#### CLOSED ISSUE BRANCHES
- Branches whose names embed an issue number (e.g. `feature/issue-123`,
  `loom/issue-123`)
- Check the linked issue: `gh issue view <number> --json state --jq .state`
- If the issue is CLOSED and no open PR exists for the branch, it's safe to delete

#### ORPHANED AUTOMATION BRANCHES
- Ephemeral branches created by tooling and abandoned — e.g. `worktree-agent-*`,
  `sync/*`, `wt/*` (Loom and similar orchestrators create these)
- Safe to delete when no active worktree uses them

#### UNKNOWN
- Any branch that doesn't match the above patterns
- Report these for manual review, do NOT auto-delete

### 3. Check worktrees for active automation

If the repo uses Loom (a `.loom/` directory exists), check each worktree's
linked issue for active labels before treating it as stale:

```bash
issue=$(echo "$branch" | grep -oE 'issue-[0-9]+' | grep -oE '[0-9]+')
gh issue view "$issue" --json state,labels --jq '[.state, (.labels[].name)] | join(",")'
```

Active labels (`loom:building`, `loom:review-requested`,
`loom:changes-requested`) mean a builder is mid-work — do NOT remove.

### 4. Present findings

```
BRANCH AUDIT
============

Local branches: 53
Worktrees: 4

SAFE TO DELETE (32 branches):
  Merged PR branches: 15
    fix/123-parser-crash (PR #150, merged 2026-06-28)
    ...
  Closed issue branches: 3
  Orphaned automation branches: 14

PROTECTED (10 branches):
  main
  feature/issue-462 (worktree active)
  ...

UNKNOWN (11 branches):
  experiment-quantizer — no PR found, no issue linked
  ...

STALE WORKTREES (0):
  (none)
```

### 5. If `--prune` flag is set

After presenting the report, delete branches in the SAFE TO DELETE category:

```bash
git branch -D <branch_name>
```

For stale worktrees:
```bash
git worktree unlock <path> 2>/dev/null
git worktree remove --force <path>
```

Report what was deleted and what remains.

### 6. If no `--prune` flag

End with:
```
To delete safe branches, run: /repo:branches --prune
To investigate unknown branches: git log --oneline -5 <branch>
```

## Safety Rules

1. **NEVER delete a branch that has an active worktree** — `git worktree remove` first
2. **NEVER delete branches with open PRs** — even if the issue is closed
3. **NEVER delete branches named as long-lived by the repo's own docs**
4. **Always report before deleting** — the user must see the full list before `--prune` acts
5. **When in doubt, classify as UNKNOWN** — let the user decide

## Notes

- PR/issue lookups need the `gh` CLI and GitHub auth; without them, fall back
  to `git branch --merged` analysis only and say so in the report
- Rate limiting: if there are hundreds of branches, batch `gh` calls
- Remote branch pruning is NOT done by this command; to prune stale remote
  tracking refs: `git fetch --prune` (safe, only removes local refs to deleted
  remote branches)
