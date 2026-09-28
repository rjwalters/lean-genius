---
name: help
description: Strictly read-only orientation — introspects the installed Anvil skills and prints what is installed, what each produces, and how to start.
---

# `/anvil:help`

Utility skill. Orients a user inside an Anvil-installed consumer repo by
introspecting **what is actually installed** and printing a two-tier help
view. **Strictly read-only** — it describes skills, it never runs them, and
it writes nothing.

## Usage

```
/anvil:help                # one-screen overview of everything installed
/anvil:help <skill>        # one skill's command set, rubric, thread layout
```

`<skill>` is a bare skill name (`memo`, `deck`, `project-scout`, …) — NOT
the `anvil-` shim prefix and NOT a command name.

## Procedure

### 1. Resolve the repo root

The repo root is the directory that contains `.anvil/` and/or `.claude/`
(the consumer install), or the Anvil source checkout itself (which has
`anvil/skills/`). This is normally the current working directory.

### 2. Run the introspection

Load the skill lib and call the single entry point. The skill's `lib/`
directory (`anvil/skills/help/lib/` in the anvil source tree,
`.anvil/skills/help/lib/` in a consumer install) is a package, not a
loose module on `sys.path` — the same shared loader every utility skill
uses (including the hyphenated ones, where a bare `sys.path.insert` +
`import <module>` fails outright) keeps this doc consistent with the
others. Use `anvil.lib.skill_lib_loader` (importable via `uv run
--project .anvil` per the "Running anvil Python from a consumer"
pattern):

```python
from pathlib import Path
from anvil.lib.skill_lib_loader import import_skill_lib_module

introspect = import_skill_lib_module(
    "help", Path("anvil/skills/help/lib"), "introspect"
)
# .anvil/skills/help/lib in a consumer install.

text = introspect.render_help(repo_root, skill=skill_name_or_None)
print(text)
```

`render_help` performs **no writes anywhere**. It reads, in priority order:

1. `.anvil/install-metadata.json` — authoritative `installed_skills`,
   `anvil_version`, per-skill `skill_versions`. Parsed defensively; a
   missing/malformed manifest is a soft-fail.
2. `.claude/skills/anvil-*/` and `.agents/skills/anvil-*/` — fallback skill
   enumeration (degraded mode, noted in output) when the manifest is
   unavailable. The former is Claude Code's shim glob, the latter Codex
   CLI's (issue #1004); both are unioned so a Codex-only install still
   reports accurately.
3. `.anvil/skills/<name>/SKILL.md` frontmatter — per-skill description +
   artifact-vs-utility classification.
4. `.anvil/skills/<name>/commands/*.md` — the real command set (the source
   of each skill's actual phase sequence — never hardcoded).
5. `.anvil/skills/<name>/rubric.md` — total + advance threshold (when
   present; artifact-class skills only).

### 3. Print the result

`render_help(repo_root)` (no skill) prints the **overview**:

- Anvil version (or a degraded-mode note when the manifest is unavailable).
- Installed skills grouped into **Artifact skills** (thread lifecycle) and
  **Utility / bridge tools** (one-shot), each with its one-line description.
- The common artifact-skill lifecycle shape
  (`draft → review → revise → (audit) → figures`) WITH the documented
  variations (essay's shorter lifecycle, report's promotion gate,
  ip-uspto's extended phases) and the caveat that utility tools have no
  lifecycle at all.
- A **"start here"** pointer using an actually-installed skill's real
  command name.

`render_help(repo_root, skill="<name>")` prints the **deep-dive**:

- An explicit **"not installed"** message when `<skill>` is not installed
  (the command describes what is installed, never what is upstream).
- The skill's description, group, full command list (from `commands/`),
  rubric summary (total + threshold, or "no rubric" / "summary
  unavailable"), and thread/version-dir layout.

## Failure modes

- **Missing / malformed manifest** → degraded mode: the skill list is
  recovered from the `.claude/skills/anvil-*/` and `.agents/skills/anvil-*/`
  shim globs and the output says so; version info is omitted. Not a hard
  error.
- **`<skill>` not installed** → an explicit not-installed message listing
  what *is* installed. No crash, no silent upstream read.
- **A `rubric.md` whose Total line doesn't match the expected pattern** →
  "rubric summary unavailable" with a pointer to the full rubric file. No
  crash.
- **Zero skills installed** (should not happen via the installer) → a clear
  "no skills detected" message. No crash.

## Read-only guarantee

The command never writes to disk and never delegates into any other skill's
commands. This matches the `project-scout` (`domain: anvil`, strictly
read-only) and `project-photos` precedents; it is SHA-256-verified in
`tests/test_help_readonly.py`.
