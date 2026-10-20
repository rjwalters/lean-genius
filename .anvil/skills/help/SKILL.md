---
name: help
description: Strictly read-only orientation for a consumer repo — introspects the installed Anvil skills (from .anvil/install-metadata.json, falling back to a directory scan) and prints what is installed, what each skill produces, and how to start. Two-tier — `anvil:help` overview, `anvil:help <skill>` deep-dive.
domain: anvil
type: skill
user-invocable: true
---

# anvil:help — Orient yourself inside an Anvil-installed repo

`anvil:help` answers the first question every user of an Anvil-installed
consumer repo has: *"what skills do I have here, what do they produce, and
how do I start?"* — without leaving the editor to read the source-repo
README.

```
/anvil:help                # one-screen overview of everything installed
/anvil:help <skill>        # one skill's command set, rubric, thread layout
```

It is the sixth utility skill (alongside `anvil:project-migrate`,
`anvil:rubric-rebackport`, `anvil:project-share`, `anvil:project-scout`,
`anvil:project-photos`, `anvil:project-book`) and, like `project-scout`
and `project-photos`, it is **strictly read-only** — it *describes* skills,
it never runs them. There is no thread, no version dir, no critic sibling,
no rubric of its own.

## Why it exists

Anvil installs a **per-consumer subset** of skills — `--skills=memo,deck`
installs only those two (`scripts/install-anvil.sh` Stage 4). The
source-repo README lists the full ~19-skill catalog, so it does not
describe any one install. And each artifact-class skill has its own command
prefix (`memo-draft`, `memo-review`, `paper-audit`, …), so a user who
forgets a skill's exact command names has no in-repo discovery path short of
`ls .claude/skills/anvil-*/` or opening a `SKILL.md` by hand. `anvil:help`
closes that gap by introspecting what is *actually installed* in the current
repo.

## Introspection sources (priority order)

`anvil:help` never hardcodes the skill catalog. It reads on-disk state:

1. **`.anvil/install-metadata.json`** (primary) — the install manifest
   written by `write_manifest()` in `scripts/install-anvil.sh`. Its
   `installed_skills` array is exactly the post-`--skills=`-filter selection
   (`SELECTED_SKILLS`), and it carries `anvil_version` and per-skill
   `skill_versions`. This is the authoritative "what's installed" list.
   Parsed **defensively** — the manifest is hand-emitted JSON via a bash
   heredoc, not schema-validated, so a missing or malformed manifest is a
   **soft-fail**, not a hard error.
2. **`.claude/skills/anvil-*/`** and **`.agents/skills/anvil-*/`** (fallback)
   — the registration shims. The former is Claude Code's; the latter is
   Codex CLI's (issue #1004, produced by `write_codex_shim()` in
   `install-anvil.sh` since #1003). When the manifest is absent (very old
   pre-manifest installs) or unparseable, the skill list is recovered by
   globbing **both** directories and stripping the `anvil-` prefix, so a
   Codex-only install (no `.claude/` at all) still reports accurately. The
   command's output notes the **degraded mode** (no version info, list is a
   directory scan) so the reader knows.
3. **`.anvil/skills/<name>/SKILL.md`** frontmatter (`name`, `description`,
   `type`, `user-invocable`) — the per-skill one-line description shown in
   both tiers, and the signal that classifies a skill as artifact-class vs
   utility/bridge-tool (see below).
4. **`.anvil/skills/<name>/commands/*.md`** — the real command set for the
   `anvil:help <skill>` deep-dive, derived from the command filenames (each
   `<name>-<phase>.md` file is one command). This is why the lifecycle is
   *introspected*, never hardcoded.
5. **`.anvil/skills/<name>/rubric.md`** (when present — artifact-class skills
   only) — the rubric total + advance threshold for the deep-dive. Absence
   is handled gracefully (utility/bridge-tool skills have no rubric).

The source-repo layout (`anvil/skills/<name>/…`, no `.anvil/` prefix) is
also recognized so the command works when run from an Anvil checkout itself,
not only from a consumer install.

## Classification: artifact skills vs utility / bridge tools

The two groups differ by their `SKILL.md` frontmatter and command shape:

| Group | `user-invocable` | Has `rubric.md` | Invoked via | Lifecycle |
|---|---|---|---|---|
| **Artifact skills** (`memo`, `deck`, `paper`, `report`, `essay`, `spec`, …) | `false` | yes | their own `<skill>-draft` / `<skill>-review` / … commands | a versioned `{thread}.{N}/` thread through `draft → review → revise → (audit) → figures` |
| **Utility / bridge tools** (`project-scout`, `project-share`, `project-photos`, `project-book`, `project-migrate`, `rubric-rebackport`, `help`) | `true` | no | directly, by name (`/anvil:<skill> …`) | none — one-shot or recurring, no thread |

## Lifecycle is NOT uniform (do not present one diagram as universal)

The `draft → review → revise → (audit) → figures` shape is the **common
shape for artifact-class skills**, not a universal law. Documented
variations the deep-dive surfaces from each skill's real command set:

- **`essay`** — `draft → review → revise → status` only. No audit, no
  figures (deliberate, per `CLAUDE.md`).
- **`report`** — adds a two-stage `AUDITED → CUSTOMER-READY` promotion gate.
- **`ip-uspto`** — extends the standard lifecycle with USPTO-specific
  phases (`s112`, `claims`, formal-compliance).
- **`primer`, `spec`** — parallel review + audit, `AUDITED`-terminal, with
  optional companion-input audits (`spec_ref` / `code_ref`).
- **Utility / bridge tools** — no `draft/review/revise` lifecycle at all;
  they are one-shot (`project-scout`, `project-share`, …) or recurring
  (`rubric-rebackport`) tools.

The overview prints the common shape **scoped to artifact skills** with an
explicit note that utility/bridge tools are one-shot commands, not lifecycle
threads. The deep-dive derives each skill's *real* phase sequence from its
`commands/` directory rather than assuming any one diagram.

## Two-tier output

### `anvil:help` (no args) — overview

- Anvil version (from manifest `anvil_version`; omitted with a degraded-mode
  note when the manifest is unavailable).
- Installed skills grouped into **Artifact skills** (thread lifecycle) and
  **Utility / bridge tools** (one-shot), each with its one-line
  `description:` from `SKILL.md` frontmatter.
- The common artifact-skill lifecycle diagram, with the utility-skill caveat.
- A **"start here"** pointer using an actually-installed skill's real command
  name — e.g. `/anvil:memo-draft <slug>` when `memo` is installed, or a
  utility skill's direct-invocation form when no artifact skill is installed.

### `anvil:help <skill>` — deep-dive

- An explicit **"not installed"** message when `<skill>` is not in
  `installed_skills` (the command describes what is *installed*, never what
  is *available upstream*).
- The skill's one-line description and group (artifact vs utility).
- Its full **command list**, derived from `commands/*.md` filenames.
- Its **rubric summary** (total + advance threshold) when `rubric.md`
  exists; a "no rubric — one-shot tool" note when it does not. A `rubric.md`
  whose Total line does not match the expected pattern degrades to "rubric
  summary unavailable" rather than crashing.
- Its **thread / version-dir layout** note for artifact skills.

## Procedure

Load the skill lib (via the shared `anvil.lib.skill_lib_loader` helper —
see `commands/help.md` for the working incantation) and call the single
entry point, passing the consumer repo root (the directory containing
`.anvil/` and/or `.claude/`) and the optional skill name:

```python
text = introspect.render_help(repo_root, skill=skill_name_or_None)
print(text)
```

`render_help` returns the operator-facing markdown/plain text and performs
**no writes anywhere**. Everything is derived from reads of the manifest and
the on-disk skill directories.

## State machine

No versioned artifact. A single read-only invocation; there is no on-disk
side effect at all (unlike `project-scout`, which can write an
operator-requested report — `help` writes nothing).

## Out of scope (v1)

- Running or delegating into any other skill's commands (read-only by
  construction; SHA-verified in tests).
- Describing upstream skills that are not installed in the current repo.
- Rendering a rubric's per-dimension weights (the summary is total +
  threshold only; the full rubric lives at `.anvil/skills/<skill>/rubric.md`).
- "Install `help` unconditionally regardless of `--skills=`" — that is an
  installer-architecture change (a new always-on skill class in Stage 4)
  orthogonal to this command; deferred to a follow-up. `help` installs as a
  normal filterable skill (default-on when no `--skills=` is passed).

## Tests

The lib loads under the unique package name `help_skill_lib` via
`tests/_help_skill_lib.py` (the #362/#367 cross-skill collision pattern).
Files (per the #58 distinct-filename convention):

- `test_help_manifest.py` — manifest parsing: well-formed, missing,
  malformed; degraded-mode fallback to the shim glob.
- `test_help_skills.py` — skill enumeration + artifact-vs-utility grouping;
  command-set derivation from `commands/*.md`.
- `test_help_rubric.py` — rubric-summary extraction against fixture
  rubric.md files (well-formed, threshold-with-bold, unmatched Total line,
  absent rubric).
- `test_help_render.py` — two-tier output: overview content, `<skill>`
  deep-dive, not-installed message, zero-skills edge case.
- `test_help_readonly.py` — SHA-256 zero-mutation contract over the repo.
