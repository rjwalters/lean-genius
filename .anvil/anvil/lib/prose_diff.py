"""Word-level prose diff engine + self-contained HTML renderer (issue #925).

Motivation
----------

`git diff` (and any line-oriented diff) is the wrong tool for prose review:
a reflowed paragraph reads as "one deleted line, one added line" even when
only three words changed, because the diff granularity is the line, not the
word. This module diffs **word tokens**, not lines, so a pure rewrap (same
words, different line breaks) renders as a near-empty diff instead of a
full-paragraph replacement.

Design
------

``diff_prose(left_text, right_text)`` tokenizes each side into a flat
stream of whitespace-run / non-whitespace-run tokens (:func:`_tokenize`),
tags every token with the **1-based source line number** it starts on
(:func:`_tokens_with_lines` — computed independently per side, from that
side's own line breaks), then runs a single
``difflib.SequenceMatcher`` over the two *whole-document* token streams.
Because the comparison is over the flat token stream rather than
line-paired blocks, a rewrap that changes line-break positions but not
word content produces a diff of just the (few) whitespace tokens that
actually changed — not a wholesale line replacement.

The result is then regrouped **per line, per side** (still driven by each
side's own line tags — the two sides are never row-aligned against each
other) so the HTML renderer can show a stable line gutter and so callers
can anchor sidecar overlay findings (`_review.json` scores, `rhetoric_lint`
findings — both keyed by 1-based line number) to the rendered line they
describe.

Stdlib only
-----------

``difflib``, ``re``, ``html``, ``dataclasses`` — nothing else. This module
is the "stdlib-only" half of the issue #925 constraint: it must be usable
(and unit-testable) with zero third-party imports, so the diff/render
core has no dependency on ``pydantic``-based modules like
``anvil.lib.review_schema`` even though a *consumer* (the ``anvil:diff``
skill) composes this module with those. Overlay data crosses this
boundary as the plain :class:`OverlayNote` dataclass, not as a
``review_schema`` type.
"""

from __future__ import annotations

import difflib
import html as _html
import re
from dataclasses import dataclass, field
from typing import List, Optional, Sequence, Tuple

__all__ = [
    "LineDiff",
    "SideDiff",
    "ProseDiffResult",
    "OverlayNote",
    "diff_prose",
    "render_html",
]


# A token is either a whitespace run or a non-whitespace run. Unicode-aware
# by default (Python 3 `str` regexes are unicode; `\S`/`\s` cover non-ASCII
# word characters and emoji as single-codepoint-or-more non-whitespace
# runs without any extra flags).
_TOKEN_RE = re.compile(r"\s+|\S+")


def _tokenize(text: str) -> List[str]:
    """Split ``text`` into whitespace-run / non-whitespace-run tokens."""

    return _TOKEN_RE.findall(text)


def _tokens_with_lines(text: str) -> List[Tuple[str, int]]:
    """Tokenize ``text`` and tag each token with its 1-based start line.

    A token is tagged with the line number that is active *before* the
    token is consumed. Only whitespace tokens can contain ``\\n`` (the
    tokenizer never splits a non-whitespace run around a newline), so a
    non-whitespace (word) token's tag is unambiguous: the exact line it
    visually sits on.
    """

    line = 1
    out: List[Tuple[str, int]] = []
    for tok in _tokenize(text):
        out.append((tok, line))
        if "\n" in tok:
            line += tok.count("\n")
    return out


# ``difflib`` opcode tag -> the per-side status this module renders. Each
# opcode names how the token span in *this* side's slice relates to the
# other side; "equal" tokens are unmarked, "delete"/"replace" tokens on the
# left are removed, "insert"/"replace" tokens on the right are added.
_STATUS_UNCHANGED = "unchanged"
_STATUS_REMOVED = "removed"
_STATUS_ADDED = "added"


@dataclass(frozen=True)
class _TaggedToken:
    text: str
    line: int
    status: str  # one of _STATUS_*


def _tag_side(
    tokens_with_lines: Sequence[Tuple[str, int]],
    start: int,
    end: int,
    status: str,
) -> List[_TaggedToken]:
    return [
        _TaggedToken(text=tok, line=ln, status=status)
        for tok, ln in tokens_with_lines[start:end]
    ]


@dataclass(frozen=True)
class OverlayNote:
    """One annotation to render alongside a diff side.

    Deliberately a plain stdlib dataclass, not a ``review_schema`` /
    ``rhetoric_lint`` type — this module stays dependency-free (see module
    docstring). Callers (the ``anvil:diff`` skill's ``lib/overlay.py``)
    translate ``Score`` / ``Finding`` / ``RhetoricFinding`` objects into
    this shape before calling :func:`render_html`.

    ``line`` is ``None`` for a document-level note (no anchor); such notes
    render in an "unanchored" section rather than inline on a line.
    """

    line: Optional[int]
    severity: str  # free-form, e.g. "warning" | "info" | "blocker" | "major" | "minor" | "nit"
    message: str
    source: str  # e.g. "rhetoric_lint" | "review:9_rhetorical_economy"


@dataclass(frozen=True)
class LineDiff:
    """One rendered line on one side of the diff."""

    line: int
    changed: bool
    html: str  # pre-escaped, word-level-highlighted inner HTML for this line


@dataclass(frozen=True)
class SideDiff:
    """The full set of rendered lines for one side of the diff."""

    lines: List[LineDiff] = field(default_factory=list)

    @property
    def changed_line_count(self) -> int:
        return sum(1 for ln in self.lines if ln.changed)


@dataclass(frozen=True)
class ProseDiffResult:
    """The output of :func:`diff_prose`: two independently line-tagged sides."""

    left: SideDiff
    right: SideDiff
    identical: bool


def _render_line_html(tokens: Sequence[_TaggedToken]) -> str:
    """Render one line's tokens to inner HTML, coalescing same-status runs."""

    if not tokens:
        return ""
    parts: List[str] = []
    run_status = tokens[0].status
    run_text: List[str] = []

    def _flush() -> None:
        if not run_text:
            return
        escaped = _html.escape("".join(run_text))
        if run_status == _STATUS_UNCHANGED:
            parts.append(escaped)
        elif run_status == _STATUS_REMOVED:
            parts.append(f"<del>{escaped}</del>")
        else:
            parts.append(f"<ins>{escaped}</ins>")

    for tok in tokens:
        if tok.status != run_status:
            _flush()
            run_status = tok.status
            run_text = []
        run_text.append(tok.text)
    _flush()
    return "".join(parts)


def _group_by_line(tokens: Sequence[_TaggedToken]) -> SideDiff:
    lines: "dict[int, List[_TaggedToken]]" = {}
    for tok in tokens:
        lines.setdefault(tok.line, []).append(tok)

    out: List[LineDiff] = []
    for line_no in sorted(lines):
        line_tokens = lines[line_no]
        changed = any(t.status != _STATUS_UNCHANGED for t in line_tokens)
        out.append(
            LineDiff(
                line=line_no,
                changed=changed,
                html=_render_line_html(line_tokens),
            )
        )
    return SideDiff(lines=out)


def diff_prose(left_text: str, right_text: str) -> ProseDiffResult:
    """Word-level diff of ``left_text`` -> ``right_text``.

    Returns a :class:`ProseDiffResult` with one :class:`SideDiff` per side,
    each a per-line rendering with word-level ``<del>``/``<ins>`` spans
    already applied. The two sides are tagged with their own independent
    line numbers (no line-pairing/row-alignment between sides) so a
    rewrap that changes line-break positions does not inflate the diff —
    see the module docstring.
    """

    left_tagged = _tokens_with_lines(left_text)
    right_tagged = _tokens_with_lines(right_text)
    left_tokens = [tok for tok, _ in left_tagged]
    right_tokens = [tok for tok, _ in right_tagged]

    matcher = difflib.SequenceMatcher(
        a=left_tokens, b=right_tokens, autojunk=False
    )

    left_out: List[_TaggedToken] = []
    right_out: List[_TaggedToken] = []
    identical = True
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            left_out.extend(_tag_side(left_tagged, i1, i2, _STATUS_UNCHANGED))
            right_out.extend(
                _tag_side(right_tagged, j1, j2, _STATUS_UNCHANGED)
            )
            continue
        identical = False
        if tag in ("delete", "replace"):
            left_out.extend(_tag_side(left_tagged, i1, i2, _STATUS_REMOVED))
        if tag in ("insert", "replace"):
            right_out.extend(_tag_side(right_tagged, j1, j2, _STATUS_ADDED))

    return ProseDiffResult(
        left=_group_by_line(left_out),
        right=_group_by_line(right_out),
        identical=identical,
    )


# ---------------------------------------------------------------------------
# HTML rendering
# ---------------------------------------------------------------------------

_PAGE_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<style>
{css}
</style>
</head>
<body>
<header>
  <h1>{title}</h1>
  <p class="subtitle">{subtitle}</p>
</header>
{unanchored_html}
<main class="panes">
  <section class="pane pane-left">
    <h2>{left_label}</h2>
    {left_html}
  </section>
  <section class="pane pane-right">
    <h2>{right_label}</h2>
    {right_html}
  </section>
</main>
<footer>
  <p>Generated by <code>anvil:diff</code> (issue #925). Read-only view —
  no edits made here are saved anywhere.</p>
</footer>
</body>
</html>
"""

_CSS = """
:root {
  color-scheme: light dark;
  --bg: #ffffff;
  --fg: #1a1a1a;
  --muted: #666666;
  --del-bg: #ffecec;
  --del-fg: #86181d;
  --ins-bg: #e6ffed;
  --ins-fg: #22863a;
  --line-changed-bg: #fffbea;
  --border: #d0d7de;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #0d1117;
    --fg: #e6edf3;
    --muted: #9198a1;
    --del-bg: #3a1414;
    --del-fg: #ffa198;
    --ins-bg: #10321c;
    --ins-fg: #7ee2a8;
    --line-changed-bg: #2b2111;
    --border: #30363d;
  }
}
* { box-sizing: border-box; }
body {
  margin: 0;
  padding: 0 0 2rem 0;
  background: var(--bg);
  color: var(--fg);
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
}
header, footer { padding: 1rem 1.5rem; }
header h1 { margin: 0 0 0.25rem 0; font-size: 1.25rem; }
.subtitle { margin: 0; color: var(--muted); font-size: 0.9rem; }
footer { color: var(--muted); font-size: 0.8rem; border-top: 1px solid var(--border); margin-top: 1rem; }
.panes {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 1px;
  background: var(--border);
  border-top: 1px solid var(--border);
  border-bottom: 1px solid var(--border);
}
.pane {
  background: var(--bg);
  overflow-x: auto;
  min-width: 0;
}
.pane h2 {
  position: sticky;
  top: 0;
  margin: 0;
  padding: 0.5rem 1rem;
  font-size: 0.95rem;
  background: var(--bg);
  border-bottom: 1px solid var(--border);
}
.line {
  display: flex;
  padding: 0.1rem 1rem;
  font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
  font-size: 0.85rem;
  white-space: pre-wrap;
  word-break: break-word;
}
.line.changed { background: var(--line-changed-bg); }
.line .ln {
  flex: 0 0 3rem;
  color: var(--muted);
  user-select: none;
  text-align: right;
  margin-right: 0.75rem;
}
.line .content { flex: 1 1 auto; }
del {
  background: var(--del-bg);
  color: var(--del-fg);
  text-decoration: line-through;
}
ins {
  background: var(--ins-bg);
  color: var(--ins-fg);
  text-decoration: none;
}
.notes { margin: 0.25rem 0 0 0; padding-left: 1.5rem; font-size: 0.78rem; }
.notes li { margin: 0.15rem 0; }
.note-blocker, .note-warning, .note-major { color: var(--del-fg); }
.note-info, .note-minor, .note-nit { color: var(--muted); }
.unanchored {
  margin: 0 1.5rem 1rem 1.5rem;
  padding: 0.75rem 1rem;
  border: 1px solid var(--border);
  border-radius: 6px;
}
.unanchored h2 { margin: 0 0 0.5rem 0; font-size: 0.95rem; }
.unanchored ul { margin: 0; padding-left: 1.25rem; font-size: 0.85rem; }
"""


def _notes_html(notes: Sequence[OverlayNote]) -> str:
    if not notes:
        return ""
    items = "".join(
        f'<li class="note-{_html.escape(n.severity)}">'
        f"<strong>[{_html.escape(n.source)}]</strong> "
        f"{_html.escape(n.message)}</li>"
        for n in notes
    )
    return f'<ul class="notes">{items}</ul>'


def _render_side(
    side: SideDiff, overlay: Optional[Sequence[OverlayNote]]
) -> str:
    by_line: "dict[int, List[OverlayNote]]" = {}
    if overlay:
        for note in overlay:
            if note.line is not None:
                by_line.setdefault(note.line, []).append(note)

    rows: List[str] = []
    for ln in side.lines:
        classes = "line changed" if ln.changed else "line"
        notes_html = _notes_html(by_line.get(ln.line, []))
        rows.append(
            f'<div class="{classes}" data-line="{ln.line}">'
            f'<span class="ln">{ln.line}</span>'
            f'<span class="content">{ln.html}{notes_html}</span>'
            f"</div>"
        )
    return "".join(rows)


def _unanchored_html(
    left_overlay: Optional[Sequence[OverlayNote]],
    right_overlay: Optional[Sequence[OverlayNote]],
) -> str:
    sections: List[str] = []
    for label, overlay in (("before", left_overlay), ("after", right_overlay)):
        if not overlay:
            continue
        unanchored = [n for n in overlay if n.line is None]
        if not unanchored:
            continue
        items = "".join(
            f'<li class="note-{_html.escape(n.severity)}">'
            f"<strong>[{_html.escape(n.source)}]</strong> "
            f"{_html.escape(n.message)}</li>"
            for n in unanchored
        )
        sections.append(
            f'<div class="unanchored"><h2>Document-level notes '
            f"({_html.escape(label)})</h2><ul>{items}</ul></div>"
        )
    return "".join(sections)


def render_html(
    result: ProseDiffResult,
    *,
    left_label: str = "before",
    right_label: str = "after",
    title: str = "anvil:diff",
    subtitle: str = "",
    left_overlay: Optional[Sequence[OverlayNote]] = None,
    right_overlay: Optional[Sequence[OverlayNote]] = None,
) -> str:
    """Render ``result`` to a single self-contained HTML page.

    No external resources — every style is inlined, there is no
    ``<script>`` and no CDN reference — so the page works fully offline
    and can be opened directly from disk as well as served locally.
    """

    if not subtitle:
        subtitle = (
            "identical — no differences"
            if result.identical
            else "word-level diff (side-by-side)"
        )

    return _PAGE_TEMPLATE.format(
        title=_html.escape(title),
        subtitle=_html.escape(subtitle),
        css=_CSS,
        unanchored_html=_unanchored_html(left_overlay, right_overlay),
        left_label=_html.escape(left_label),
        right_label=_html.escape(right_label),
        left_html=_render_side(result.left, left_overlay),
        right_html=_render_side(result.right, right_overlay),
    )
