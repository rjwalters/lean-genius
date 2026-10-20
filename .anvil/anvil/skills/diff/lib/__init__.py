"""Skill-local lib for `anvil:diff` (issue #925).

Modules:

- ``sources``: input-mode resolution -- version-dir pairs (through
  ``anvil.lib.latest_resolution.resolve_latest``), deslop-run pairs
  (``emit/cleaned.txt`` against an origin file), and body-file lookup
  inside a version dir. Filesystem-shape-only; never reads file
  *content* and never writes anything.
- ``overlay``: translates ``.review/`` sidecar critic output
  (``anvil.lib.critics`` / ``anvil.lib.review_schema``) and
  ``anvil.lib.rhetoric_lint`` findings into the plain
  ``anvil.lib.prose_diff.OverlayNote`` shape the renderer consumes.
  Read-only, non-throwing (a missing/malformed sidecar degrades to an
  empty overlay).
- ``server``: the localhost-only, ephemeral-port HTTP server wrapper
  around a pre-rendered HTML string. No auth, no daemon, no state
  directory; binds ``127.0.0.1`` only.

The actual word-level diff + self-contained HTML render lives in
``anvil.lib.prose_diff`` (promoted straight to ``anvil/lib/`` rather
than skill-local, per the issue's design -- it is a cross-cutting
primitive over ANY skill's version dirs, not specific to this skill).
See ``commands/diff.md`` for the runnable CLI entry point
(``lib/cli.py``).
"""
