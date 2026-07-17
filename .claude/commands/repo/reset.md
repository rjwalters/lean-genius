---
name: "reset"
description: "Return the repo to a clean baseline — review stale worktrees/branches/stashes, sync with remote, land back on the default branch"
domain: repo
type: command
user-invocable: true
---

# /repo:reset — Back to Baseline

The end-of-task ritual: review and prune stale git state, sync with the
remote, and land back on the default branch with a clean working tree.
Report-first — nothing is deleted or dropped without appearing in the report
and getting a yes.

## Usage

```
/repo:reset                    # Interactive: review everything, act on approval
/repo:reset --prune            # Also delete confirmed-safe branches/worktrees without per-item prompts
```

## Steps

### 1. Working tree safety check

```bash
git status --porcelain
```

If the tree is dirty, stop and resolve it **first** — everything after this
step assumes no work can be lost. Show the changes and ask:
- **Commit** them (offer to draft the commit)
- **Stash** them with a descriptive message (`git stash push -m "..."`)
- **Abort** the reset and leave everything as is

NEVER discard changes. `git checkout --`, `git reset --hard`, and `git clean`
on tracked modifications are off the table unless the user explicitly asks.

### 2. Stash review

```bash
git stash list --format='%gd %cr %gs'
```

For each stash, show what's in it (`git stash show --stat <ref>`) and its age.
Ask per stash: **apply**, **drop**, or **keep**. Old stashes (>30 days) are
usually droppable but the user decides — never auto-drop.

### 3. Branch & worktree review

Run the full [[branches]] classification (PROTECTED / merged-PR / closed-issue
/ orphaned-automation / UNKNOWN, plus stale worktrees). With `--prune`, delete
the SAFE TO DELETE category after presenting it; otherwise ask.

### 4. Sync with remote

```bash
git fetch --all --prune
```

Then return to the default branch and fast-forward it:

```bash
default=$(git symbolic-ref --short refs/remotes/origin/HEAD | sed 's|origin/||')
git checkout "$default"
git pull --ff-only
```

If `--ff-only` fails, the local default branch has diverged from the remote —
report the divergence (`git log --oneline @{u}..HEAD` and `HEAD..@{u}`) and
ask how to proceed. Do not rebase or force anything on your own.

### 5. Final state report

```
RESET COMPLETE
==============
Branch:    main (up to date with origin/main)
Tree:      clean
Stashes:   1 kept (stash@{0}: "wip: quantizer experiment", 3 days old)
Branches:  4 deleted, 2 UNKNOWN kept (experiment-a, spike/cache)
Worktrees: 1 removed (../repo-wt-fix123)
```

List anything intentionally left behind so nothing is silently forgotten.

## Related

- Filesystem clutter (build artifacts, caches, temp files) is [[tidy]]'s job —
  offer to run it after the reset if the inventory looked messy
- Deep branch analysis and its safety rules live in [[branches]]
