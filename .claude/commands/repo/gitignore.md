---
name: "gitignore"
description: "Audit gitignore rules — find over-ignored files and under-ignored build artifacts"
domain: repo
type: command
user-invocable: true
---

# /repo:gitignore — Gitignore Audit

Check that gitignore rules are appropriate for this repository. Catches files
that shouldn't be ignored and build artifacts that should be.

## Usage

```
/repo:gitignore                  # Full repo
/repo:gitignore data/            # Check one subtree
```

## Context First

Determine whether the repo is public or private before judging rules
(`gh repo view --json isPrivate --jq .isPrivate`, or ask the user if there is
no GitHub remote). The right answer differs:
- **Private repos** often want data files, docs, and notes *tracked* — flag
  rules that hide them.
- **Public repos** often want those same files *ignored* — flag tracked files
  that look like they leaked in (credentials, dumps, personal notes are
  critical findings either way).

## What It Checks

### 1. Over-Ignored Files
Flag gitignore rules that exclude things that look like real content:
- Data files (.yaml, .json, .csv) that aren't build output
- Documentation or notes
- Configuration that isn't secrets

**Always keep ignored, in any repo:**
- `.env` files and anything credential-like
- `node_modules/`, `.venv/`, `__pycache__/`
- Build output (`dist/`, `build/`, `target/`, `*.pyc`)
- IDE files (`.vscode/`, `.idea/`)
- OS files (`.DS_Store`)

### 2. Under-Ignored Files
Find tracked files that are probably build artifacts:
- `*.pyc`, `__pycache__/`
- `dist/`, `build/`, coverage output
- Large binaries that look generated (`.o`, `.so`, `.whl`)

### 3. Gitignore Hygiene
- Redundant rules (already covered by a parent `.gitignore`)
- Rules that match zero files (stale after cleanup)
- Scattered `.gitignore` files that could be consolidated

### 4. Large Untracked Files
Find untracked files >1 MB that might need a decision:
- Should they be tracked? (data files, docs)
- Should they be gitignored? (build output, caches)
- Should they live outside the repo? (measurement data, large datasets —
  object storage, LFS, or a NAS)

## Interaction

For each `.gitignore` file, show:
- Current rules and what they match
- Suggested additions or removals
- Files affected by changes

Ask before modifying any gitignore.
