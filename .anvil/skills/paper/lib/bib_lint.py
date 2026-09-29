"""Deterministic BibTeX syntax pre-flight for ``anvil:paper``'s litsearch phase.

Motivating incident (issue #998, 2026-08-12): a consumer's
``paper-litsearch`` run wrote a bare ``@article`` token inside a
``%``-prefixed "comment" block in ``candidates.bib``. ``candidates.bib``
is never compiled by the litsearch phase itself, so the defect stayed
latent until ``paper-draft`` merged candidate entries into the version's
``refs.bib`` and ``bibtex`` failed downstream — harder to trace back to
its origin at that point, and had to be repaired by hand.

This module is the paper-skill analog of ``anvil/lib/render_gate.py`` /
``anvil/skills/paper/lib/artifact_verify.py``: a cheap, deterministic
pre-flight gate that catches a structural defect *before* it propagates,
per the framework's "deterministic pre-flight before judgment" convention
(``CLAUDE.md`` § Pattern overview).

Why a structural scan, not a real ``bibtex`` invocation
---------------------------------------------------------

BibTeX has **no block-comment syntax** — text between recognized
``@type{key, ...}`` entries is simply skipped as junk *until the scanner
hits the next literal ``@`` character*, at which point it unconditionally
tries to parse a new entry starting there. A bare ``@article`` sitting
inside prose (even prose meant as a comment) trips this scanner exactly
the same way a real, intended entry would. This module reproduces that
scanning behavior deterministically in pure Python — no ``bibtex`` binary
required, so **no availability/graceful-degradation gate is needed**
(unlike, say, ``anvil/lib/render.py``'s ``check_*_available()`` family):
the check always runs, with no external dependency to be absent.

Skill-local first (``CLAUDE.md`` "wait for the second consumer before
generalizing"): ``paper-litsearch`` is the only current writer of
``candidates.bib``. Promote to ``anvil/lib/`` (candidate home:
``anvil/lib/cite.py``, which already owns BibTeX formatting/writing) only
if a second skill needs the same check.

What it catches
----------------

1. **A bare ``@<word>`` token outside a recognized entry** — any literal
   ``@`` that is not immediately (module whitespace) followed by an
   identifier and an opening ``{``/``(`` that begins a real
   ``@type{key, ...}`` entry. This is the reported failure mode: a
   discussion sentence like "there's also @article-type work on X" trips
   the scanner exactly like BibTeX's own would.
2. **Unbalanced braces within an entry** — an ``@type{`` (or ``@type(``)
   entry whose body never reaches a matching closing brace/paren before
   end of file.

What it does NOT flag (by design, matching real BibTeX behavior)
------------------------------------------------------------------

- A literal ``@`` character that occurs *inside* a brace-balanced entry
  body (e.g. an email-address-shaped string in an ``author``/``note``
  field, ``foo@bar.com``) — this text is consumed as part of the entry's
  body via brace-depth tracking, never re-examined for a stray ``@``.
- Multiple well-formed entries separated by ``%``-prefixed comment lines
  that carry no ``@`` character of their own.

See ``anvil/skills/paper/tests/test_paper_bib_lint.py`` for the
regression fixture reproducing the reported shape.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List

# Matches a literal '@' followed (module optional whitespace) by an
# entry-type identifier and the opening delimiter of a real BibTeX entry
# (``{`` or ``(``). BibTeX entry types allow letters/digits/underscore/
# hyphen (``@online``, ``@in-proceedings``-style extensions in some
# styles); we accept the permissive superset rather than a fixed
# allowlist, since BibTeX itself does not restrict entry-type spelling.
_ENTRY_START_RE = re.compile(r"@\s*([A-Za-z][A-Za-z0-9_-]*)\s*([{(])")

# Kinds surfaced in ``BibLintIssue.kind`` / the JSON payload.
KIND_STRAY_AT = "stray_at"
KIND_UNBALANCED_BRACES = "unbalanced_braces"

_SNIPPET_WIDTH = 88


@dataclass
class BibLintIssue:
    """One structural defect found in a ``.bib`` file."""

    kind: str  # KIND_STRAY_AT | KIND_UNBALANCED_BRACES
    line: int  # 1-based line number where the issue starts
    message: str
    snippet: str  # trimmed excerpt of the offending line, for context

    def to_dict(self) -> dict:
        return {
            "kind": self.kind,
            "line": self.line,
            "message": self.message,
            "snippet": self.snippet,
        }


@dataclass
class BibLintResult:
    """Outcome of one ``lint_bib_text``/``lint_bib_file`` pass."""

    issues: List[BibLintIssue] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        """``True`` only when the scan found zero structural issues."""
        return not self.issues

    def to_dict(self) -> dict:
        return {"ok": self.ok, "issues": [i.to_dict() for i in self.issues]}


def _line_number(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def _line_snippet(text: str, pos: int, width: int = _SNIPPET_WIDTH) -> str:
    line_start = text.rfind("\n", 0, pos) + 1
    line_end = text.find("\n", pos)
    if line_end == -1:
        line_end = len(text)
    snippet = text[line_start:line_end].strip()
    if len(snippet) > width:
        snippet = snippet[: width - 1] + "…"
    return snippet


def lint_bib_text(text: str) -> BibLintResult:
    """Scan raw BibTeX source for structural defects.

    Reproduces BibTeX's own entry-scanning behavior: repeatedly find the
    next literal ``@``, require it to open a real ``@type{key, ...}`` (or
    ``@type(...)``) entry, and — when it does — consume a brace-balanced
    body before resuming the search. See the module docstring for the
    full rationale and the two issue kinds this emits.
    """
    issues: List[BibLintIssue] = []
    i = 0
    n = len(text)

    while i < n:
        at = text.find("@", i)
        if at == -1:
            break

        m = _ENTRY_START_RE.match(text, at)
        if not m:
            # A bare '@' (or one not immediately followed by a real
            # `type{`/`type(` opener) outside any recognized entry.
            # BibTeX has no comment syntax, so this is exactly the
            # scanner-trip the reported defect produced.
            issues.append(
                BibLintIssue(
                    kind=KIND_STRAY_AT,
                    line=_line_number(text, at),
                    message=(
                        "stray '@' is not immediately followed by a "
                        "recognized `@type{...}` / `@type(...)` entry "
                        "opener; BibTeX has no comment syntax and will "
                        "try to parse this as a new entry."
                    ),
                    snippet=_line_snippet(text, at),
                )
            )
            i = at + 1
            continue

        open_ch = m.group(2)
        close_ch = "}" if open_ch == "{" else ")"
        entry_type = m.group(1)
        body_start = m.end()

        depth = 1
        j = body_start
        while j < n and depth > 0:
            ch = text[j]
            if ch == open_ch:
                depth += 1
            elif ch == close_ch:
                depth -= 1
            j += 1

        if depth > 0:
            issues.append(
                BibLintIssue(
                    kind=KIND_UNBALANCED_BRACES,
                    line=_line_number(text, at),
                    message=(
                        f"entry '@{entry_type}{open_ch}…' starting here "
                        f"never reaches a matching closing '{close_ch}' "
                        "before end of file."
                    ),
                    snippet=_line_snippet(text, at),
                )
            )
            # Nothing after an unterminated entry can be scanned
            # reliably (the rest of the file reads as its "body").
            break

        # A well-formed, brace-balanced entry — resume scanning after
        # it. Any '@' characters inside its body (e.g. an email address
        # in a field value) were already consumed by the depth-balanced
        # walk above and are never re-examined.
        i = j

    return BibLintResult(issues=issues)


def lint_bib_file(path: Path) -> BibLintResult:
    """Read ``path`` and run :func:`lint_bib_text` over its contents."""
    text = Path(path).read_text(encoding="utf-8")
    return lint_bib_text(text)


__all__ = [
    "KIND_STRAY_AT",
    "KIND_UNBALANCED_BRACES",
    "BibLintIssue",
    "BibLintResult",
    "lint_bib_text",
    "lint_bib_file",
]
