r"""Recursive ``\input``/``\include`` resolver for multi-file LaTeX threads.

Issue #643: ``paper`` is the one anvil skill explicitly designed for
genuinely multi-file LaTeX documents — a master ``main.tex`` that
``\input{sections/...}``s many section files is a normal, expected
whitepaper shape. But the review/verify pipeline historically named only
the master file (``paper-review.md`` step 4 "load ``main.tex``", the
``source_paths`` list at step 4b, and ``evidence_check.py``'s single-file
body detection), so a reviewer that obeyed the literal instruction scored
a near-empty ~90-line shell against the /44 rubric and silently missed the
entire paper body.

There is (was) **no** ``\input``/``\include`` resolver anywhere in the
codebase — ``render_gate.py``'s ``source_paths`` is a caller-supplied path
list, not a walker (verified in the issue #643 curation). This module is
the missing primitive. It ships lib-scoped (not skill-local) because three
consumers exist on day one: (1) ``paper-review.md`` step 4's content read,
(2) step 4b's render-gate ``source_paths`` construction, and (3)
``evidence_check.py``'s quote-verification body (a reviewer that now reads
the full body but whose quote-verifier only checks ``main.tex`` would
otherwise emit false ``fabricated_evidence`` findings for legitimate quotes
drawn from ``\input``-ed children).

Resolver behavior (each verified explicitly in ``tests/lib/test_tex_includes.py``):

- Recognizes ``\input{path}`` and ``\include{path}`` (braced form) and the
  brace-less ``\input path`` form (whitespace-terminated).
- ``.tex`` extension defaulting: ``\input{sections/intro}`` resolves to
  ``sections/intro.tex``; ``\input{sections/intro.tex}`` (extension already
  present) is NOT doubled to ``sections/intro.tex.tex``.
- Nested ``\input``: a child that itself ``\input``s further files is
  walked recursively (depth-first, document order).
- Comment-awareness: an ``\input{...}`` after an unescaped ``%`` on the
  same line (a LaTeX comment) is NOT resolved — reuses the same
  comment-masking primitive precedent as ``numeric_consistency._mask_text``
  (``latex=True``): the ``(?<!\\)%[^\n]*`` rule.
- Missing target: an ``\input``/``\include`` whose file is absent on disk
  does NOT crash — it is surfaced as a ``missing`` entry (a dangling
  ``\input`` is itself useful reviewer signal: a broken document).
- Cycle guard: two files ``\input``-ing each other (malformed but possible)
  do NOT infinite-loop — visited real paths are tracked.

The module is pure-stdlib (no third-party deps), mirroring
``numeric_consistency.py``'s subprocess-free posture.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional


# ---------------------------------------------------------------------------
# Comment masking (shared precedent with numeric_consistency._mask_text)
# ---------------------------------------------------------------------------

# An unescaped ``%`` starts a LaTeX comment to end-of-line. ``\%`` is a
# literal percent and does NOT start a comment. Identical rule to
# ``numeric_consistency._LATEX_COMMENT_RE`` — a documented sharp edge this
# codebase already masks for the same reason (a commented-out ``\input``
# must not be resolved as a real include).
_LATEX_COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")


def _strip_latex_comments(text: str) -> str:
    """Blank every LaTeX comment region to spaces, preserving newlines.

    Masking (rather than deleting) keeps line numbers stable so a future
    caller wanting line anchors can map back to the source. Matches the
    offset-preserving discipline of ``numeric_consistency._mask_text``.
    """

    def blank(m: "re.Match[str]") -> str:
        return "".join(c if c == "\n" else " " for c in m.group(0))

    return _LATEX_COMMENT_RE.sub(blank, text)


# ---------------------------------------------------------------------------
# \input / \include extraction
# ---------------------------------------------------------------------------

# Braced form: ``\input{path}`` / ``\include{path}``. The path is any run
# of non-``}`` characters (LaTeX paths never contain a literal ``}``).
_BRACED_INCLUDE_RE = re.compile(r"\\(?:input|include)\s*\{([^}]*)\}")

# Brace-less ``\input`` form: ``\input path`` — TeX accepts this, the path
# runs to the next whitespace. ``\include`` requires braces in LaTeX, so we
# only support the brace-less form for ``\input`` (matching TeX semantics).
# The negative lookahead ``(?!\s*\{)`` keeps this from double-matching the
# braced form above.
_BARE_INPUT_RE = re.compile(r"\\input(?!\s*\{)\s+([^\s%{}]+)")


def _extract_targets(text: str) -> List[str]:
    """Return the raw ``\\input``/``\\include`` target strings in document order.

    Comments are masked first so a commented-out include is invisible.
    """
    masked = _strip_latex_comments(text)
    hits: List[tuple[int, str]] = []
    for m in _BRACED_INCLUDE_RE.finditer(masked):
        target = m.group(1).strip()
        if target:
            hits.append((m.start(), target))
    for m in _BARE_INPUT_RE.finditer(masked):
        target = m.group(1).strip()
        if target:
            hits.append((m.start(), target))
    hits.sort(key=lambda pair: pair[0])
    return [target for _, target in hits]


def _candidate_paths(target: str, including_dir: Path, job_dir: Path) -> List[Path]:
    r"""Return the candidate filesystem paths for a raw ``\input`` target.

    ``.tex`` extension defaulting: a target with no ``.tex`` suffix gets one
    appended (``sections/intro`` → ``sections/intro.tex``); a target that
    already ends in ``.tex`` is left alone (no ``.tex.tex`` doubling).

    Two resolution roots are tried, in order:

    1. The **job directory** (``job_dir``, the master file's directory) —
       LaTeX's own semantics: a compile run is rooted at the master, so
       ``\input``/``\include`` targets (even inside nested children) are
       conventionally written relative to the job root. This is the
       overwhelmingly common real-paper shape (e.g. a ``sections/method.tex``
       that ``\input{sections/details}`` — the path is job-relative, not
       child-relative).
    2. The **including file's directory** (``including_dir``) — the fallback
       for the rarer relative-to-child authoring style.

    The first candidate that exists on disk wins (checked by the caller);
    both are returned so a fully-missing target can report the job-relative
    form (candidate 1) as its canonical ``missing`` entry.
    """
    if not target.endswith(".tex"):
        target = target + ".tex"
    job_candidate = job_dir / target
    including_candidate = including_dir / target
    # De-dup when the two roots coincide (master \input-ing a sibling).
    if job_candidate == including_candidate:
        return [job_candidate]
    return [job_candidate, including_candidate]


# ---------------------------------------------------------------------------
# Result type
# ---------------------------------------------------------------------------


@dataclass
class ResolvedTex:
    r"""Result of resolving a master ``.tex`` file's ``\input``/``\include`` tree.

    Attributes:
        files: The resolved files in depth-first document order, master
            FIRST, then each ``\input``/``\include`` child (and its own
            children, recursively). Every entry is an existing file on
            disk. De-duplicated: a file included twice appears once, at its
            first-seen position (the cycle/repeat guard).
        missing: ``(target, including_file)`` pairs for every
            ``\input``/``\include`` whose resolved path does not exist on
            disk — surfaced, never raised. A non-empty ``missing`` list is
            useful reviewer signal (a dangling include is a broken document).
        body: The concatenated text of every file in ``files``, in order,
            joined by a single newline. This is the reviewable document —
            the master PLUS its resolved children — for scoring,
            quoted-evidence checks, and section-keyed comments.
    """

    files: List[Path] = field(default_factory=list)
    missing: List[tuple] = field(default_factory=list)
    body: str = ""

    @property
    def has_missing(self) -> bool:
        return bool(self.missing)


def resolve_tex_inputs(
    master: Path,
    *,
    encoding: str = "utf-8",
) -> ResolvedTex:
    r"""Recursively resolve a master ``.tex`` file's ``\input``/``\include`` tree.

    Walks ``master`` depth-first in document order, following each
    ``\input``/``\include`` child (with ``.tex`` extension defaulting,
    LaTeX-comment awareness, and a cycle/repeat guard). Missing targets are
    collected in :attr:`ResolvedTex.missing` rather than raising — a
    dangling include is surfaced as reviewer signal, not a crash.

    Args:
        master: Path to the master file (e.g. ``<thread>.{N}/main.tex``).
        encoding: Text encoding for reads (default ``utf-8``).

    Returns:
        A :class:`ResolvedTex` whose ``files`` lists every resolved file
        (master first), ``missing`` lists dangling includes, and ``body``
        is the concatenated reviewable document.

    Raises:
        FileNotFoundError: only when ``master`` itself does not exist. A
        missing CHILD is surfaced in ``missing``, never raised.
    """
    master = Path(master).resolve()
    if not master.is_file():
        raise FileNotFoundError(
            f"tex_includes: master file {master!s} does not exist."
        )

    result = ResolvedTex()
    visited: set = set()
    job_dir = master.parent

    def walk(path: Path) -> None:
        real = path.resolve()
        if real in visited:
            # Cycle / repeat guard: a file included twice (or two files
            # \input-ing each other) is walked once, at first-seen position.
            return
        visited.add(real)
        try:
            text = real.read_text(encoding=encoding)
        except OSError:
            # Unreadable file that nonetheless exists — treat like a missing
            # target for robustness (never crash the resolver).
            result.missing.append((str(real), str(path)))
            return
        result.files.append(real)
        for target in _extract_targets(text):
            candidates = _candidate_paths(target, real.parent, job_dir)
            hit = next((c for c in candidates if c.is_file()), None)
            if hit is not None:
                walk(hit)
            else:
                result.missing.append((target, str(real)))

    walk(master)
    result.body = "\n".join(
        f.read_text(encoding=encoding) for f in result.files
    )
    return result


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.tex_includes",
        description=(
            "Recursively resolve a master .tex file's \\input/\\include "
            "tree. Prints the resolved file list (master first, "
            "document order) and any dangling includes. Missing children "
            "are surfaced, never fatal."
        ),
    )
    p.add_argument(
        "master",
        help="Path to the master .tex file (e.g. <thread>.{N}/main.tex).",
    )
    p.add_argument(
        "--print-body",
        action="store_true",
        help="Print the concatenated reviewable body to stdout.",
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Exit codes:
    - ``0``: resolved with no missing includes.
    - ``1``: resolved but ≥1 dangling ``\\input``/``\\include`` (surfaced).
    - ``2``: invocation error (master file missing).
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)
    try:
        result = resolve_tex_inputs(Path(args.master))
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print("resolved files (document order):")
    for f in result.files:
        print(f"  {f}")
    if result.missing:
        print("dangling includes:", file=sys.stderr)
        for target, including in result.missing:
            print(f"  {target!r} (from {including})", file=sys.stderr)
    if args.print_body:
        print("---8<--- body ---8<---")
        print(result.body)
    return 1 if result.missing else 0


__all__ = [
    "ResolvedTex",
    "resolve_tex_inputs",
    "main",
]


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
