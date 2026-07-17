---
name: "readme"
description: "Check README accuracy against actual directory contents and offer to update"
domain: repo
type: command
user-invocable: true
---

# /repo:readme — README Check

Validate that READMEs accurately describe the directories they live in. Catches
stale file trees, incorrect descriptions, and missing READMEs in significant
directories.

## Usage

```
/repo:readme                    # Scan all READMEs in repo
/repo:readme packages/core      # Scope to one subtree
/repo:readme docs/README.md     # Check a specific README
```

## What It Checks

### 1. File Tree Accuracy
If a README contains an ASCII file tree (```...``` block with `├──` or `└──`),
compare it against the actual directory listing:
- Files/dirs listed in README but missing on disk
- Files/dirs on disk but not listed in README
- Descriptions that are factually wrong (e.g., "gitignored" when it's tracked)

### 2. Missing READMEs
Flag directories that probably need one:
- Any directory with >5 files and no README
- Any top-level package/project directory without a README
- Skip: `node_modules/`, `.git/`, `__pycache__/`, virtualenvs, build output dirs

### 3. Stale Content
- References to removed files or directories
- "TODO" or "WIP" markers older than 30 days (check git blame)
- References to tools or workflows that no longer exist in the repo

## Interaction

For each finding, show the specific discrepancy and ask whether to:
1. **Update the README** to match reality (add/remove entries)
2. **Skip** this finding
3. **Show me the README** so I can decide

When updating, preserve the README's existing style and voice — just fix the
factual inaccuracies.
