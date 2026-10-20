---
name: project-scout
description: Repo-wide read-only discovery of anvil-adoptable document clusters — classified adoption report with per-cluster recommended commands.
---

# `/anvil:project-scout`

Utility skill. Surveys a tree and reports where the anvil-adoptable
documents are. **Strictly read-only** — there is no apply mode; the only
writes are the operator-requested report paths.

## Usage

```
/anvil:project-scout <root>
    [--include <glob> ...]     # positive filter on candidate FILES
    [--exclude <glob> ...]     # prune whole subtrees (recorded, named)
    [--report <path>]          # write the markdown report to <path>
    [--json <path>]            # write the versioned JSON sidecar to <path>
    [--verbose]                # list NOT_DOCUMENT files + signal detail
```

`<root>` is typically a repo root or a top-level docs tree — NOT a single
project dir (that is `project-migrate`'s contract). Direct `--report` /
`--json` paths **outside** the scanned tree (e.g. `/tmp/scout.md`); the
scan itself never writes.

## Procedure

### 1. Run the scan

Load the skill lib and call the single entry point. The skill's `lib/`
directory (`anvil/skills/project-scout/lib/` in the anvil source tree,
`.anvil/skills/project-scout/lib/` in a consumer install) is a package
whose modules import each other by relative import (`from .cluster import
...`), and the directory name is hyphenated, so it cannot be loaded with a
bare `sys.path.insert` + `import orchestrate`. Use the shared loader
(`anvil.lib.skill_lib_loader`, importable via `uv run --project .anvil`
per the "Running anvil Python from a consumer" pattern):

```python
from pathlib import Path
from anvil.lib.skill_lib_loader import import_skill_lib_module

orchestrate = import_skill_lib_module(
    "project-scout", Path("anvil/skills/project-scout/lib"), "orchestrate"
)
# .anvil/skills/project-scout/lib in a consumer install.

result = orchestrate.run(
    root,
    include=include_globs,      # () when not given
    exclude=exclude_globs,      # () when not given
    verbose=verbose,
    report_path=report_path,    # None when not given
    json_path=json_path,        # None when not given
)
```

`result.markdown` is the operator-facing report — print it. `result.data`
is the JSON sidecar dict (`schema_version: 1`). `result.success` is False
only when the root is missing or the coverage identity is violated (a
scout bug — surface `result.warnings` loudly).

### 2. Read the report

One section per bucket, in action order:

- **LEGACY_MIGRATABLE** — run `/anvil:project-migrate <dir>` (dry-run
  first, as always with the bridge tools).
- **BARE_THREADS** — run `/anvil:project-migrate <dir>`. The BRIEF is
  synthesized automatically for the bare shape (post-#411); the dry-run
  shows the proposed BRIEF with `# TODO(operator)` markers. There is no
  separate flag.
- **LOOSE_DOCUMENTS** — run `/anvil:project-migrate --enroll <file>`
  per candidate (or the surfaced batch glob form for a directory of
  candidates). Low-confidence entries carry no command — verify before
  enrolling; the per-file signal list shows why the heuristic fired.
- **FOREIGN_GRAMMAR** — report-only. Each family carries a `why`
  explaining how it diverges from the canonical `{stem}.{N}` /
  single-dot-free-tag grammar. Do NOT run migrate on these roots (the
  guard exists because `detect_shape` would misclassify them as
  migratable).
- **ALREADY_MIGRATED** — nothing to do.
- **NOT_DOCUMENT** — counted; listed under `--verbose`.

Then the honest-coverage tail: pruned subtrees (every default exclude,
dotdir, and `--exclude` hit is named) and the coverage table with the
identity `candidate_files == in_clusters + loose_classified +
not_document`.

### 3. Act (separately, per cluster)

Scout never acts. Each recommended command is an existing sibling
capability; run them one cluster at a time, dry-run first.

## Failure modes

- Nonexistent root → `success=False`, empty report, warning naming the
  path.
- Coverage-identity violation → `success=False` with a warning asking for
  the JSON sidecar in a bug report (files are never silently dropped; an
  identity break means a scout bug, not operator error).
- A nominated root that classifies UNKNOWN is surfaced in the
  Diagnostics section and its files flow through the loose-file path —
  counted, never lost.

## Determinism

Two runs over the same tree produce byte-identical output (sorted paths,
no timestamps) — safe to diff across adoption sessions.
