# Version and critic sibling directory layout

Canonical naming convention for anvil artifact directories. Every skill
follows this layout; the discovery logic in `thread_state.md` and
`critics.md` depends on it.

## Directory taxonomy

Given a thread slug `<thread>` (e.g., `acme-seed`, `q3-method`,
`kdd-2026-keynote`, `acme-widget`), a portfolio contains these
directory kinds:

| Kind | Pattern | Purpose | Mutability |
|---|---|---|---|
| **Thread root** | `<thread>/` | Brief, refs, per-thread overrides | Mutable (human-edited) |
| **Version** | `<thread>.{N}/` | One drafted version of the artifact | Immutable once `_progress.json` records `done` |
| **Critic sibling** | `<thread>.{N}.<tag>/` | Output of one critic on version N | Immutable once written |
| **Pre-draft sibling** | `<thread>.0.<tag>/` | Pre-draft phase output (e.g., outline, litsearch) | Immutable once written |
| **Project root** | `<project>/` | Per-project shared context (report skill) | Mutable (`_project.md`) |
| **Terminal sibling** | `<thread>.{N}.<tag>/` (e.g., `.handout/`, `.promote/`) | Terminal-state export or acknowledgment | Immutable once written |

## Naming rules

1. **Version numbering**: integer, starting at `1` for the first drafted
   version. No zero-pad (`acme-seed.1/`, not `acme-seed.01/`). Versions
   are dense — there are no gaps in a normal lifecycle.
2. **Critic tag**: a single short token, no nested dots, no spaces. Use
   `review`, `audit`, `s101`, `narrative`, `market`, `design`,
   `preflight`, `litsearch`, `outline`, `rehearse`, `handout`, `promote`.
3. **Pre-draft phase tag**: special case — a sibling at `<thread>.0.<tag>/`
   may exist before any `<thread>.1/`. Reserved for outputs that feed
   the first drafter (outline for slides, litsearch for paper, brief intake
   for deck).
4. **Final-package suffix**: `<thread>.final/` is reserved for skills
   that produce a separate assembled submission package (e.g.,
   ip-uspto's filing bundle). This is NOT a critic sibling; it does not
   carry a numeric version suffix.

## Discovery globs

A reviser or orchestrator discovers what exists for a thread by globbing:

```
<thread>.{N}/              All versioned dirs (sort by N to find latest).
<thread>.{N}.*/            All critic siblings for version N.
<thread>.0.*/              All pre-draft siblings.
<thread>.final/            Optional terminal submission package.
```

To find the latest version:

```
latest_N = max(N for N in versions_dirs(<thread>))
```

To find all critic siblings for the latest version:

```
glob("<thread>.{latest_N}.*/")  minus the bare "<thread>.{latest_N}/"
```

## Portfolio placement

The discovery globs above read relative to the **portfolio directory** —
the parent that contains `<thread>/`, `<thread>.{N}/`, and
`<thread>.{N}.<tag>/` siblings. Anvil does **not** constrain where the
portfolio dir lives in the consumer repo. Two common organizations:

- **Filetype-first**: one portfolio per artifact type.

  ```
  output/
    decks/<thread>/, <thread>.1/, <thread>.1.review/, …
    memos/<thread>/, <thread>.1/, <thread>.1.review/, …
    research/<thread>/
  ```

  Optimizes for "show me all decks" workflows. Each skill's
  discover-glob runs inside its own portfolio (`output/decks/`,
  `output/memos/`).

- **Project-first**: one portfolio per project/venture, shared across
  artifact types.

  ```
  output/
    <thread>/                     Project root (doubles as portfolio for every skill)
      <thread>/                   Anvil thread root (BRIEF.md, refs/, assets/)
      <thread>.0/, <thread>.1/, <thread>.1.review/, …     Anvil deck/slides/paper
      memo.1/, memo.1.review/, …                          Other skill (e.g., studio memo)
      research/                                            Non-anvil artifacts
  ```

  Optimizes for "show me everything about project X" workflows. The
  per-project portfolio dir IS the project dir; the per-skill
  discover-glob runs inside it and naturally only matches that skill's
  `<thread>.*` siblings.

  The visible cost is the `<thread>/<thread>/` repetition inside the
  project dir (the anvil thread root reuses the project slug). This is
  intentional: the inner `<thread>/` is what discover-glob looks for,
  so the slug must match. Mildly ugly, functional.

Choose based on whether the consumer thinks about artifacts ("show me
all decks") or about projects/ventures ("show me everything about X").
Studios with many concurrent projects (the 2AM Logic Studio canary
runs 15+ ventures) typically prefer project-first; single-project
consumers typically prefer filetype-first.

Either way, the rest of this snippet (directory taxonomy, naming
rules, discovery globs, immutability) applies unchanged.

## N+1 allocation

When a reviser produces the next version after consuming all `<thread>.{N}.*/`
critic siblings, the next version is `<thread>.{N+1}/`. The reviser MUST:

1. Verify `<thread>.{N+1}/` does not already exist (a partially-failed
   revise should be cleaned up via the crash recovery contract).
2. Carry forward `metadata.iteration` as `N+1` and preserve
   `metadata.max_iterations` from the prior version's `_progress.json`
   (or inherit from `<thread>/.anvil.json`).

## `<thread>.0.<tag>/` rationale

Why `0` for pre-draft siblings? It places them in the orchestrator's
enumeration alongside other siblings (which use `<N>.<tag>/` shapes),
preserving the "glob `<thread>.*` and parse" discovery pattern. Three
skills currently use this:

- `slides.0.outline/` — narrative outline before draft.
- `paper.0.litsearch/` — pre-draft literature search.
- `deck.0/` (no tag) — brief-intake output (special case: bare `.0/`
  carries `BRIEF.md` itself).

When an orchestrator detects a gap (e.g., `<thread>.0.outline/` exists
but no `<thread>.1/`), the state is `OUTLINED` (or `BRIEF_DONE`, etc.,
per the skill's state machine), not an anomaly.

## Convenience `.latest` symlinks (framework-maintained by default, consumer-pinnable)

Convenience symlinks per thread alias the highest-N version of a
thread:

```
<thread>.latest        -> <thread>.{max_N}/
<thread>.latest.review -> <thread>.{max_N}.review/
<thread>.latest.<tag>  -> <thread>.{max_N}.<tag>/      e.g., .latest.design, .latest.audit
```

They exist to give human operators and downstream tooling a stable
path that always resolves to the current version (no N-parsing
required).

**Contract** (issue #473; previously "optional and consumer-maintained"
— the studio canary surfaced that the consumer-side convention was
agent-invisible): skills that have adopted the writer (today:
`anvil:memo`) maintain `<thread>.latest` and `<thread>.latest.review`
**by default** at the end of each lifecycle write (draft / review /
revise), via the canonical writer
`anvil.lib.latest_resolution.update_latest_symlinks()` exposed through
a per-skill phase CLI (memo: `anvil/skills/memo/lib/latest_phase.py`).
Each suffix family is handled independently with **relative** targets
(`ln -sfn` semantics); already-existing `<thread>.latest.<tag>`
families are re-pointed too, but the framework never invents new tag
families. Skills that have not yet adopted the writer remain on the
consumer-maintained convention.

**Consumer-pinnable**: the writer discriminates the steady-lifecycle
stale link (still on the immediately-superseded version, set before
the new highest dir existed — re-pointed freely; this is the tracking
path) from an intentional pin: any other symlink that resolves to a
real, **non-highest** version dir (e.g., "publish `.latest` against
the reviewed-and-AUDITED v3 even though v4 is in progress") is
presumptively an operator pin and is preserved with a notice —
`--force` re-points. A real `.latest/` *directory* (non-symlink) is never
replaced. Dangling symlinks are repaired freely. The writer is
idempotent and non-blocking. The symlinks are framework-maintained
output but never framework *input*: no shipped command requires them
to exist, and deleting them breaks nothing.

### Discovery-glob guarantee

The discovery enumeration documented in `thread_state.md` (lines 33–53)
matches only directories whose suffix is a digit-N, optionally followed
by an alphanumeric critic tag:

| Pattern enumerated | Regex |
|---|---|
| `<thread>.{N}/`        | `^<slug>\.(\d+)$` |
| `<thread>.{N}.<tag>/`  | `^<slug>\.(\d+)\.([a-zA-Z0-9-]+)$` |

A `.latest` (or `.latest.review`, `.latest.design`, …) suffix is **not**
a digit and is therefore **invisible** to the version and sibling
enumerators — even when the symlink resolves to a real directory. The
`enumerate_versions` / `enumerate_siblings` functions in
`thread_state.md` return the same list whether or not `.latest`
symlinks are present in the portfolio directory.

This is the load-bearing guarantee for the convention: a consumer who
adds `<thread>.latest -> <thread>.{max_N}` does not perturb anvil's
state-machine derivation. The symlinks are inert from the framework's
perspective.

### Typical usage

After a memo lifecycle command writes `<thread>.{N+1}/` (or a
`.review/` sibling), the command's final step invokes the latest-phase
CLI, which re-points each family atomically (the `ln -sfn` idiom,
implemented as create-temp-then-rename):

```
python3 .anvil/skills/memo/lib/latest_phase.py <thread-dir>     # [--force]
```

Downstream tools (figure scripts cross-referencing another thread,
share scripts pointing at "the current PDF", `pdfinfo` checks in CI)
can then hardcode `<thread>.latest/...` and never go stale. Figure
scripts in particular can reference other-skill artifacts via stable
paths like `refs/<thread>.latest/...` rather than hardcoding
`refs/<thread>.8/...`, which silently goes stale on the next revision.

For skills that have not yet adopted the writer, the consumer-side
idiom remains `ln -sfn <thread>.{N+1} <thread>.latest` after each
write (the studio canary's ~80-line `output/refresh-latest-symlinks.sh`
sweep script is the precedent). Consumer scripts and the framework
writer compose safely: both are idempotent and both preserve
resolvable non-highest pins only if written to do so — the framework
writer always does.

### Edge cases worth noting

- **Git tracks symlink targets as text.** Updating
  `memo.latest -> memo.7` to `memo.latest -> memo.8` is a one-line
  semantic diff, which makes version bumps self-documenting in commit
  history.
- **`git status` shows symlinks as modified when the target changes.**
  This is the desired behavior — the version bump is visible.
- **Some web servers don't follow symlinks** (Apache MultiViews,
  restrictive S3 configs). Edge case for consumers who publish
  artifact trees over HTTP without an explicit copy step.
- **Cross-platform**: macOS Finder and GNU/Linux `ls` follow symlinks
  natively; Windows shells handle them via WSL or `mklink /D`.

### Promotion history

The refresh logic was consumer-side in v0 per the "wait for the second
consumer before generalizing" rule (CLAUDE.md). The convention was then
observed load-bearing in the wild (every studio thread carries the
symlinks) while remaining agent-invisible — so issue #473 shipped the
predicted shape: `anvil.lib.latest_resolution.update_latest_symlinks()`
called from the end of each successful memo lifecycle write
(`memo-draft` / `memo-review` / `memo-revise`, via
`anvil/skills/memo/lib/latest_phase.py`). Other skills (`deck`,
`datasheet`, …) adopt in follow-ups once the memo shape settles.

## Immutability contract

A directory becomes immutable once its `_progress.json` records the
relevant phase as `done`. After that point:

- The reviser, orchestrator, and any other agent treats the directory
  as read-only.
- Files are never edited in place. To "fix" something, produce a new
  version (`<thread>.{N+1}/`) with a `changelog.md` explaining what
  changed.
- The exception is the thread root (`<thread>/`), which is mutable
  because the brief and refs are author-editable inputs, not
  artifact outputs.

## See also

- `thread_state.md` — derive state-machine position from on-disk layout.
- `critics.md` — discover and aggregate critic siblings.
- `progress.md` — `_progress.json` schema and merge rules.
