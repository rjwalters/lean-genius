"""Shared parsing/scanning helpers for the render-gate (issue #1128 split).

``pdfinfo`` resolution + page counting, the TeX-log file-scope-stack
walker (issue #961), the overfull-box log parser (issue #668 dedupe),
the pending-marker-aware placeholder scanner (issue #842), and the
LaTeX engine-error extractor. Split out of the former monolithic
``anvil/lib/render_gate.py`` along its existing section banners — see
``anvil/lib/render_gate/__init__.py`` for the full package rationale.
"""

from __future__ import annotations

import bisect
import re
import shutil
import subprocess
from pathlib import Path
from typing import Iterable, Optional

from anvil.lib.render_gate.constants import (
    _FILE_OPEN_RE,
    _LATEX_ERROR_RE,
    _OVERFULL_RE,
)




def _which_pdfinfo(override: Optional[str]) -> Optional[str]:
    """Resolve the ``pdfinfo`` executable path, honoring the override."""
    if override is not None:
        return override
    return shutil.which("pdfinfo")


def _count_pages_with_pdfinfo(
    pdf_path: Path, *, pdfinfo_path: Optional[str] = None
) -> Optional[int]:
    """Return the page count of a PDF via ``pdfinfo``, or ``None`` if
    unavailable / unparsable.

    Surfaces ``None`` rather than raising — the gate is supposed to degrade
    cleanly when poppler is absent (same pattern as ``render.py`` does with
    ``pdftoppm`` falling back to ``pdf2image``).
    """
    exe = _which_pdfinfo(pdfinfo_path)
    if exe is None:
        return None
    if not pdf_path.exists():
        return None
    try:
        proc = subprocess.run(
            [exe, str(pdf_path)],
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, FileNotFoundError):
        return None
    if proc.returncode != 0:
        return None
    # pdfinfo prints lines like "Pages:           42"
    for line in proc.stdout.splitlines():
        if line.lower().startswith("pages:"):
            try:
                return int(line.split(":", 1)[1].strip())
            except (ValueError, IndexError):
                return None
    return None


def _file_scope_transitions(log_text: str) -> tuple[list[int], list[Optional[str]]]:
    """Walk the TeX log's parenthesis-delimited file-open/close scope stack.

    TeX/LaTeX engines announce "now processing this file" as a bare
    ``(<path>`` (no intervening whitespace) and close it with a matching
    ``)`` once control returns to the including file — the same
    convention used for class/style files (``(./anvil-uspto.cls)``) and for
    nested ``\\input``/``\\include`` targets (``(./claims.tex ... )``).
    Non-file parenthesized text (hyperref chatter, "(see the log for
    details)", etc.) still opens/closes a stack frame — it just isn't
    *tagged* as a file frame — so file-frame nesting stays correct even
    when interleaved with unrelated parens.

    Returns two parallel lists ``(positions, files)`` sorted by ascending
    log offset: ``positions[i]`` is the log offset at which the innermost
    open file became ``files[i]`` (``None`` before the first file-open, e.g.
    the engine banner lines). Feed this into :func:`_file_at_offset` to
    resolve "which file was open when this log offset was emitted" for any
    match position.
    """
    positions: list[int] = []
    files: list[Optional[str]] = []
    file_stack: list[str] = []
    # Parallel to the *full* paren stack (file + non-file frames) so a close
    # paren always pops the correct kind of frame — a non-file paren nested
    # inside an open file frame must not accidentally pop the file frame.
    is_file_frame: list[bool] = []
    length = len(log_text)
    i = 0
    while i < length:
        ch = log_text[i]
        if ch == "(":
            m = _FILE_OPEN_RE.match(log_text, i)
            if m:
                name = Path(m.group("path")).name
                file_stack.append(name)
                is_file_frame.append(True)
                positions.append(i)
                files.append(name)
            else:
                is_file_frame.append(False)
        elif ch == ")":
            if is_file_frame:
                was_file = is_file_frame.pop()
                if was_file and file_stack:
                    file_stack.pop()
                    positions.append(i + 1)
                    files.append(file_stack[-1] if file_stack else None)
        i += 1
    return positions, files


def _file_at_offset(
    positions: list[int], files: list[Optional[str]], offset: int
) -> Optional[str]:
    """Return the file open at ``offset`` per the ``_file_scope_transitions``
    lists, or ``None`` if no file-open precedes ``offset``."""
    idx = bisect.bisect_right(positions, offset) - 1
    if idx < 0:
        return None
    return files[idx]


def _parse_overfull_boxes(
    log_text: str, threshold_pt: float, *, root_name: Optional[str] = None
) -> list[dict]:
    """Return the list of overfull-box hits exceeding ``threshold_pt``.

    Each entry: ``{kind, amount_pt, line, file, raw}``. Threshold is
    strictly greater than: a 5.0pt-over-threshold-5.0 box is NOT reported
    (matches typical LaTeX overfull tolerance — exactly-at-threshold boxes
    are cosmetic).

    **File attribution (issue #961).** A box's "at lines NN--MM" span is
    TeX's line count *within whichever file is currently open* — when a
    parent document ``\\input``s a child (``spec.tex`` pulling in
    ``claims.tex``), a box emitted while the child is open reports line
    numbers relative to the child, not the parent. We resolve the file
    each hit actually belongs to by replaying the log's
    ``(./file.tex ... )`` scope stack (:func:`_file_scope_transitions`) up
    to the hit's log offset, so ``file`` is the innermost open file at that
    point — ``claims.tex``, not the top-level ``spec.tex``, for a box
    emitted between the child's open and close markers. When the log has
    no recognizable file-open marker at all (e.g. a synthetic log with no
    preamble), ``file`` falls back to ``root_name`` (typically the
    top-level ``.tex`` file's basename, when the caller has it) or
    ``None``.

    **Dedupe contract (issue #668).** Multi-pass LaTeX cycles
    (``pdflatex → bibtex → pdflatex → pdflatex``, as captured by
    e.g. ``paper-audit``'s ``compile-log.txt``) re-emit the *same* overfull
    warning on every ``pdflatex`` invocation, so a single real overfull box
    appears once per pass in the concatenated log. We deduplicate by
    ``(file, line, amount_pt, kind)`` — LaTeX line numbers are stable
    across passes for line-anchored warnings (hbox ``at lines N--M``, vbox
    ``detected at line N``), so identical tuples are re-emissions of the
    same underlying box, not independent defects. First occurrence wins, so
    ``line``/``file``/``raw``/``kind`` reflect the first pass's text and
    single-pass logs (no duplicate tuples) are returned byte-identically.

    Hits with no captured ``line`` (the regex line-span group is absent)
    are **never** collapsed together: a genuinely line-less log with several
    distinct warnings would otherwise degenerate to one entry. Only hits
    with ``line is not None`` participate in dedupe; line-less hits are all
    preserved in insertion order.

    The dedupe changes only count/cardinality, never presence — the
    verdict logic in :func:`gate` is presence-based (``if overfull:``), so a
    log that flagged before still flags after.
    """
    hits: list[dict] = []
    seen: set[tuple[Optional[str], int, float, str]] = set()
    positions, files = _file_scope_transitions(log_text)
    for m in _OVERFULL_RE.finditer(log_text):
        amount = float(m.group("amount"))
        if amount <= threshold_pt:
            continue
        line_start = m.group("line_start")
        line = int(line_start) if line_start else None
        kind = f"{m.group('kind').lower()}box"
        file_name = _file_at_offset(positions, files, m.start()) or root_name
        if line is not None:
            key = (file_name, line, amount, kind)
            if key in seen:
                continue
            seen.add(key)
        hits.append(
            {
                "kind": kind,
                "amount_pt": amount,
                "line": line,
                "file": file_name,
                "raw": m.group(0).strip(),
            }
        )
    return hits


# Well-formed pending-marker span (issue #842). A ``[PENDING <source>]`` /
# ``[PENDING: <source>]`` placeholder is a *permitted* honest disclosure (a
# value that does not exist yet), NOT a generic incompleteness placeholder —
# so a placeholder-pattern hit that falls inside a well-formed pending marker
# is excluded from Check 6. Kept as a local literal (rather than importing
# ``pending_marker``) to avoid coupling the render gate's import graph to it;
# the two regexes are documented to agree.
_RENDER_GATE_PENDING_MARKER_RE = re.compile(
    r"\[PENDING(?:\s*:\s*|\s+)[^\]\n]+?\s*\]"
)


def _pending_marker_spans(line: str) -> list[tuple[int, int]]:
    """(start, end) offsets of every well-formed pending marker in ``line``."""
    return [m.span() for m in _RENDER_GATE_PENDING_MARKER_RE.finditer(line)]


def _scan_placeholders(
    source_paths: Iterable[Path],
    patterns: tuple[str, ...],
) -> list[dict]:
    """Grep each ``source_path`` for any of ``patterns``.

    Each match: ``{pattern, path, line, match}``. Files that fail to read
    (binary, missing) are silently skipped — the gate's job is to surface
    matches, not to fail on a malformed input.

    Well-formed ``[PENDING <source>]`` markers (issue #842) are carved out:
    a placeholder hit whose span falls inside a pending marker on the same
    line is skipped, so the generic placeholder scan never double-flags (and
    hard-fails on) a marker this convention explicitly permits.
    """
    if not patterns:
        return []
    compiled = [(p, re.compile(p)) for p in patterns]
    hits: list[dict] = []
    for path in source_paths:
        if not path.exists() or not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            pending_spans = _pending_marker_spans(line)
            for pattern_str, regex in compiled:
                m = regex.search(line)
                if not m:
                    continue
                # Carve-out: skip a hit that overlaps a well-formed pending
                # marker (issue #842).
                ms, me = m.span()
                if any(ps <= ms and me <= pe for ps, pe in pending_spans):
                    continue
                hits.append(
                    {
                        "pattern": pattern_str,
                        "path": str(path),
                        "line": lineno,
                        "match": m.group(0),
                    }
                )
    return hits


def _extract_engine_errors(log_text: str, max_lines: int = 10) -> list[str]:
    """Return the last ``max_lines`` lines starting with ``!`` (LaTeX errors)."""
    matches = _LATEX_ERROR_RE.findall(log_text)
    if not matches:
        return []
    return [m.strip() for m in matches[-max_lines:]]

