---
name: diff
description: Local, read-only, word-level side-by-side prose diff viewer — anvil version dirs, a deslop origin/cleaned pair, or two arbitrary files, with an optional .review/ sidecar + rhetoric_lint overlay. Serves on 127.0.0.1; never writes to any input path.
---

# `/anvil:diff`

Utility skill. Renders a word-level, side-by-side HTML diff between two
prose sources and serves it locally for interactive review. **Strictly
read-only over every input path** — the only path it can ever write to
is an operator-named `--out` file, and only when that flag is passed.

## Usage

```
/anvil:diff versions <thread-dir> <slug> [--from N] [--to N] [--no-review-overlay]
/anvil:diff deslop <thread-dir> --origin <path>
/anvil:diff files <left> <right>
```

Shared flags (all three modes):

```
--left-label <text>       # override the left-pane heading
--right-label <text>      # override the right-pane heading
--lint {left,right,both,none}   # rhetoric-lint overlay side(s); default: right
--port <N>                 # bind this port instead of an OS-assigned one
--no-serve                  # print the HTML to stdout instead of serving it
--out <path>                # also write the rendered HTML to this path
```

## Runnable entry point

The flow ships as a directly runnable argparse CLI, `lib/cli.py`
(mirroring `project-share/lib/cli.py`). From a **consumer repo root**
(where anvil is installed under `.anvil/`):

```
python3 .anvil/anvil/skills/diff/lib/cli.py versions <thread-dir> <slug>
python3 .anvil/anvil/skills/diff/lib/cli.py deslop <thread-dir> --origin <path>
python3 .anvil/anvil/skills/diff/lib/cli.py files <left> <right>
```

From the **anvil source repo** the path is
`anvil/skills/diff/lib/cli.py` instead.

The CLI bootstraps `sys.path` (walking up to the ancestor carrying
`anvil/__init__.py`, so both layouts resolve) and loads the sibling
`lib/` package via `anvil.lib.skill_lib_loader` — no hand-rolled
importlib driver needed. It prints diagnostics to stderr and exits
nonzero on a resolution failure (missing version dir, missing origin
file, missing `emit/cleaned.txt`). If the anvil framework itself cannot
be imported (e.g. `pydantic` missing because `uv sync --project .anvil`
never ran), it prints a remediation and exits 1; under `uv`, invoke it
as `uv run --project .anvil python .anvil/anvil/skills/diff/lib/cli.py
<mode> ...`.

## Procedure

### 1. Resolve the input pair

- **`versions`** — `lib/sources.py::resolve_version_pair(thread_dir,
  slug, from_n=..., to_n=...)` resolves `{slug}.{N}` vs `{slug}.{N+1}`
  through the canonical resolver (`anvil.lib.latest_resolution.resolve_latest`), which tolerates every on-disk shape (pinned symlink, real directory, or walk-to-highest), so an operator's pin is honored.
  `--to` defaults to the highest resolvable version; `--from` defaults
  to the version immediately before it.
  `resolve_body_file` then locates each version dir's body file
  (`<slug>.md`, then `<slug>.tex`, then a size-based fallback). A
  single-version thread with no explicit `--from` raises a clean error
  naming the flag to pass, rather than crashing.
- **`deslop`** — `lib/sources.py::resolve_deslop_pair(thread_dir,
  origin)` requires `emit/cleaned.txt` to exist under `thread_dir`
  (written by `anvil/skills/deslop/lib/orchestrate.py::emit`) and
  `origin` to exist on disk (deslop never persists the origin path, so
  it must be supplied here). Returns the rationale path too, when
  `emit/rationale.md` exists.
- **`files`** — the two paths are used directly; each must exist.

### 2. Read + diff

Read both resolved files as UTF-8 text (the only file reads this
command performs) and call
`anvil.lib.prose_diff.diff_prose(left_text, right_text)` — a
word-level diff over the whole document's token stream (not
line-paired), so a pure rewrap does not read as a full-paragraph
replacement. Each side is tagged with its OWN 1-based line numbers
(no row-alignment between sides).

### 3. Assemble the overlay(s)

- `versions` mode (unless `--no-review-overlay`): for BOTH resolved
  version dirs, `lib/overlay.py::load_review_overlay(version_dir)`
  discovers every `.review`-shaped critic sibling
  (`anvil.lib.critics.discover_critics` / `load_review`) and translates
  scores (skipping unowned/`None` dims) and findings into overlay
  notes, anchored to a line when `evidence_span` carries one
  (`<path>:L<start>-L<end>`), else rendered as a document-level note.
  Non-throwing: a missing sibling or malformed `_review.json` degrades
  to fewer notes, never an exception.
- `--lint {left,right,both,none}`: for the selected side(s),
  `lib/overlay.py::load_rhetoric_lint_overlay(text)` runs
  `anvil.lib.rhetoric_lint.lint_rhetoric` and translates its findings
  (each already carries a real 1-based `line`, or `None`).
- `deslop` mode: `emit/rationale.md`'s bullet list (when present) is
  attached to the "cleaned" side as document-level notes (the
  underlying data has no per-hunk anchor to attach to).

### 4. Render + serve

`anvil.lib.prose_diff.render_html(...)` produces one self-contained
HTML string (no CDN assets, no `<script>`). Then:

- Default: `lib/server.py::build_server` binds `127.0.0.1` on an
  OS-assigned ephemeral port (or `--port`) and
  `serve_until_interrupt` prints the URL and serves until `Ctrl+C`,
  closing the socket cleanly on exit.
- `--no-serve`: skip the server; print the HTML to stdout (unless
  `--out` was also given, in which case only the write-confirmation
  line prints).
- `--out <path>`: also write the HTML to `<path>` — the ONLY path this
  command ever writes to, and only on this explicit flag.

## Failure modes

- **Version dir / body file not found** (`versions` mode) — a clean
  `VersionPairError` message on stderr naming the missing path; exit 1.
  No output written.
- **`emit/cleaned.txt` or `--origin` missing** (`deslop` mode) — same
  shape: clean message, exit 1.
- **Arbitrary file missing** (`files` mode) — same shape: clean
  message, exit 1.
- **Missing/malformed `.review/` sidecar** — never a hard error; the
  overlay for that critic sibling is simply omitted (see step 3).
- **Zero rhetoric-lint findings** — the lint overlay section is simply
  absent from the rendered page; not an error.

## Read-only guarantee

No input path (version dir, `.review/` sidecar, origin file, arbitrary
file) is ever written to, in any mode — verified by
`tests/test_diff_readonly.py`'s SHA-256 zero-mutation contract. The
server itself (`lib/server.py`) never re-opens a filesystem path at
request-handling time; it serves the same in-memory HTML string built
once at startup. Binds `127.0.0.1` only (`lib/server.py::ALLOWED_HOST`)
— no network exposure, no auth needed, no daemon.
