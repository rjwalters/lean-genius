---
name: diff
description: Local, ephemeral, read-only word-level side-by-side prose diff viewer — compares two anvil version dirs, a deslop origin/cleaned pair, or two arbitrary files, with an optional `.review/` sidecar + rhetoric_lint overlay. Stdlib-only, localhost-bound, never writes to any input path.
domain: anvil
type: skill
user-invocable: true
---

# anvil:diff — Local side-by-side prose diff viewer

`anvil:diff` renders a **word-level**, side-by-side HTML diff between two
prose sources and serves it on `127.0.0.1` for one browser tab. It exists
because `git diff` (and any line-oriented diff) is the wrong tool for prose
review: a reflowed paragraph reads as "one deleted line, one added line"
even when three words changed. `anvil:diff` diffs word tokens, not lines,
so a pure rewrap renders as a near-empty diff instead of a wholesale
paragraph replacement.

```
python3 .anvil/anvil/skills/diff/lib/cli.py versions <thread-dir> <slug> [--from N] [--to N]
python3 .anvil/anvil/skills/diff/lib/cli.py deslop <thread-dir> --origin <path>
python3 .anvil/anvil/skills/diff/lib/cli.py files <left> <right>
```

(from the anvil source repo the path is
`anvil/skills/diff/lib/cli.py`; see `commands/diff.md` for the full
invocation, including the `uv run --project .anvil` form.)

It is the eighth utility skill (alongside `anvil:project-migrate`,
`anvil:rubric-rebackport`, `anvil:project-share`, `anvil:project-scout`,
`anvil:project-photos`, `anvil:project-book`, `anvil:help`) and, like
`anvil:help`, is **strictly read-only** — it never writes into a version
dir, an origin file, or any other input path. The only path it ever
writes is an operator-chosen `--out` file, and only when that flag is
passed; the default behavior (serve, or `--no-serve` with no `--out`)
writes nothing to disk at all. It is also the first utility skill that
produces a **transient view** rather than a filesystem artifact — a
genuinely new output category for anvil (see the issue's "open questions
for curation").

## Why it exists

Every revise pass produces a new immutable `{thread}.{N}/` version dir.
Comparing N to N+1 today means either eyeballing two files side by side
or running `git diff`, which is line-oriented and near-useless on
rewrapped prose. Review output and body text also live in different
files (`_review.json` sidecar vs. the body markdown/LaTeX), so deciding
whether a revise pass actually addressed a dim 9 finding means holding
two files and a JSON payload in your head. `anvil:diff` turns that into
one screen: the word-level diff, with rubric scores and `rhetoric_lint`
findings annotated inline on the lines they describe.

## Three input modes

1. **`versions <thread-dir> <slug> [--from N] [--to N]`** — the default
   and most common case. Resolves `{slug}.{N}` vs `{slug}.{N+1}` through
   `anvil.lib.latest_resolution.resolve_latest` (an operator's `.latest`
   pin is honored, matching every other `.latest` consumer in the
   framework). `--to` defaults to the `.latest`-resolved version;
   `--from` defaults to the version immediately before it. A
   single-version thread (nothing to diff yet) is a clean error, not a
   crash — pass `--from` explicitly once a second version exists. The
   body file inside each version dir is located by
   `lib/sources.py::resolve_body_file` (`<slug>.md`, then `<slug>.tex`,
   then a size-based fallback).
2. **`deslop <thread-dir> --origin <path>`** — diffs an
   `anvil:deslop` run's origin file against the `emit/cleaned.txt` it
   wrote (see `anvil/skills/deslop/lib/orchestrate.py::emit`), and
   attaches `emit/rationale.md`'s bullet list as document-level notes on
   the "cleaned" side. `anvil:deslop` never persists the origin path, so
   it must be supplied here explicitly.
3. **`files <left> <right>`** — the escape hatch: diff two arbitrary
   paths directly. No anvil-specific overlay context is inferred in this
   mode (there is no version dir or `.review/` sidecar concept for an
   arbitrary file pair) — the deterministic rhetoric-lint overlay still
   applies when `--lint` requests it.

## Sidecar overlay

The differentiator is not the diff — it is the diff **annotated with
anvil's own signals**, so "read the review JSON, then find the paragraph
it means" becomes one screen:

- **`.review/` sidecar** (`versions` mode only, unless `--no-review-overlay`):
  every critic sibling of each version dir (`anvil.lib.critics
  .discover_critics` / `load_review`) is translated into per-dimension
  score notes and per-finding notes. A note anchors to a line when the
  critic's `evidence_span` carries one (the documented
  `<path>:L<start>-L<end>` format — see `anvil/lib/review_schema.py`);
  otherwise it renders as a document-level note in an "unanchored"
  rail at the top of the page.
- **`rhetoric_lint`** (`--lint {left,right,both,none}`, default
  `right`): runs the deterministic `anvil.lib.rhetoric_lint` pass over
  the selected side(s) and renders each finding inline on the line it
  fired on (or as a document-level note when the finding is not
  line-anchored). This is where the #919 rule work becomes directly
  visible on the text it flags, instead of living in a JSON blob.

Both overlays **degrade gracefully**: a missing `.review/` sibling, a
malformed `_review.json`, or zero lint findings all render a perfectly
usable page with that section simply omitted — never an exception. See
`lib/overlay.py` for the non-throwing contract.

## Constraints (load-bearing, not decoration)

- **Stdlib only.** The diff engine and HTML renderer
  (`anvil.lib.prose_diff`) import only `difflib`, `html`, `re`,
  `dataclasses` — no web framework, no third-party HTML templating.
  Verified by `tests/lib/test_prose_diff.py`'s AST import-discipline
  check. The rendered page has **no CDN assets and no `<script>`** — it
  is a single self-contained HTML file that works fully offline.
- **Read-only, always.** No input path (version dir, origin file,
  `.review/` sidecar, arbitrary file) is ever written to. Verified by
  `tests/test_diff_readonly.py`'s SHA-256 zero-mutation contract across
  all three modes. There is **no in-browser editing** in v1 — "apply
  this hunk" is a deliberately deferred v2 design question (see
  Non-goals).
- **Localhost bind, ephemeral, no auth.** `lib/server.py::build_server`
  only ever binds `127.0.0.1` (`ALLOWED_HOST`) on an OS-assigned
  ephemeral port (`port=0` by default). No daemon, no state directory,
  no persistence between runs.

## Procedure

1. Resolve the input pair for the requested mode via `lib/sources.py`
   (`resolve_version_pair` / `resolve_deslop_pair` / a direct path pair
   for `files`).
2. Read both files' text (the only file reads this skill performs).
3. Diff the text with `anvil.lib.prose_diff.diff_prose` — word-level,
   per-side line tagging.
4. Assemble the overlay(s) via `lib/overlay.py`
   (`load_review_overlay` / `load_rhetoric_lint_overlay`) per the
   requested mode and `--lint` selection.
5. Render the self-contained page with
   `anvil.lib.prose_diff.render_html`.
6. Serve it via `lib/server.py` (`build_server` +
   `serve_until_interrupt`), printing the URL — or, with `--no-serve`,
   print the HTML to stdout / write it to `--out`.

## State machine

None. `anvil:diff` has no thread, no version dir, no critic sibling, no
rubric of its own — a single read-only invocation per run, like
`anvil:help`. Unlike `anvil:help` (which writes nothing at all), this
skill can optionally write ONE operator-named output file (`--out`), but
never touches an input path.

## Non-goals (v1)

- A general-purpose git diff viewer — scoped to anvil version dirs and
  deslop output; use `git diff` for arbitrary repo history.
- Editing, applying hunks, or writing anything back to a version dir.
  This needs its own design discussion about which file an "apply"
  would even target, given version-dir immutability.
- Serving beyond localhost, or persisting state between runs.
- Replacing the review sidecar as the source of truth — this skill
  *reads* `_review.json`; it never becomes a second place review state
  lives.
- A unified-diff toggle / watch-mode auto-refresh — both flagged as
  open questions in the issue, deferred to a follow-up rather than
  bundled into this scope.

## Tests

The lib loads under the unique package name `diff_lib` via
`tests/_diff_skill_lib.py` (the #362/#367 cross-skill collision
pattern). Files (per the #58 distinct-filename convention):

- `tests/lib/test_prose_diff.py` (top-level, since `anvil.lib.prose_diff`
  is a promoted framework primitive, not skill-local) — identical text,
  pure-rewrap minimal diff, insertions/deletions, non-ASCII/emoji
  tokens, HTML self-containment, overlay rendering, stdlib-only import
  discipline.
- `anvil/skills/diff/tests/test_diff_sources.py` — body-file resolution,
  version enumeration, version-pair resolution (including the pinned
  `.latest` symlink case), deslop-pair resolution.
- `anvil/skills/diff/tests/test_diff_overlay.py` — review-sidecar
  translation (scores + findings, evidence_span line-anchoring, missing/
  malformed-sidecar graceful degradation), rhetoric-lint translation.
- `anvil/skills/diff/tests/test_diff_server.py` — loopback bind + real
  ephemeral-port fetch (200 + body match), `serve_until_interrupt`'s
  print-then-close contract.
- `anvil/skills/diff/tests/test_diff_cli.py` — all three modes end to
  end, stdlib-only module-level imports, error paths.
- `anvil/skills/diff/tests/test_diff_readonly.py` — SHA-256 zero-mutation
  contract across all three modes plus the `--out`-is-the-only-write
  contract.
