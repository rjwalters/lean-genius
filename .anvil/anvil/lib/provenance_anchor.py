"""Deterministic ``provenance.md`` anchor-drift advisory (issue #868).

The problem
-----------

The local-corpus claim-provenance contract (issue #597,
``anvil/lib/snippets/provenance.md``) has each ``provenance.md`` row cite
its supporting corpus passage by a bare ``Source file`` + ``Line range``.
That address is not stable: any mid-file edit of the corpus file (an
insertion above the cited passage, a reflow, an appended correction) can
silently shift every row that cites a later line — the citation still
*resolves* to a range, just the wrong text. A spot-sampling reviewer
reading plausible text at the (now-wrong) cited range passes it; only an
exhaustive corpus audit that re-opens every range catches the drift, and
only if it re-runs after the corpus changed.

This module implements the fix's mechanical half: each provenance row MAY
carry an **``Anchor``** column — a short verbatim quoted snippet drawn
from the cited passage — which is the row's true, content-addressed
identity. The ``Line range`` column is demoted to a *hint*: cheap to
read, but not authoritative. This module:

1. **Resolves** each row's anchor against the on-disk corpus file,
   searching the WHOLE file (not just the hinted range) for the anchor
   text and classifying the outcome (:data:`STATUS_RESOLVED` /
   :data:`STATUS_DRIFTED` / :data:`STATUS_NOT_FOUND` /
   :data:`STATUS_FILE_NOT_FOUND` / :data:`STATUS_NO_ANCHOR`).
2. **Repoints** drifted rows mechanically — rewriting only the ``Line
   range`` cell to the anchor's actual current location, leaving
   ``Claim`` / ``Source file`` / ``Anchor`` / ``Notes`` untouched. This is
   explicitly NOT the "fabricating a source-line mapping" failure the
   drafter/reviser contract prohibits: the anchor text itself already
   proves the citation is genuine, this only corrects a stale hint.

Distinct from :mod:`anvil.lib.evidence_drift` (issue #857, BRIEF/refs
mtime staleness) and :mod:`anvil.lib.probe_freshness` (issue #863,
perishable external claims). Both of those detect that a *verification*
has gone stale because something *outside* the citation moved. This
module detects that the citation's own *address* has gone stale because
the *cited file* moved underneath it — the evidence never changed, only
where it lives. See ``anvil/lib/snippets/provenance.md`` §"Relationship
to #863" for the boundary discussion.

Backward compatibility
-----------------------

A ``provenance.md`` row written before this feature has no ``Anchor``
column value (either the whole table predates the 5-column shape, or an
individual row's ``Anchor`` cell is empty). Both are reported as
:data:`STATUS_NO_ANCHOR` — never an error, never a false drift signal.
Drift detection is simply unavailable for that row until the next
draft/revise pass adds an anchor. This mirrors
:mod:`anvil.lib.evidence_drift`'s ``STATUS_NO_SNAPSHOT`` bootstrap
posture: unknown is honest, never conflated with "not drifted" OR with
"drifted".

Matching is exact-after-normalization (curly quotes folded to straight,
whitespace runs collapsed to a single space), case-sensitive — the same
verbatim-quote discipline as ``anvil/lib/evidence_check.py``, applied to
corpus passages instead of a reviewed body.

CLI entry-point
----------------

``python -m anvil.lib.provenance_anchor check <provenance.md> <corpus_root> [<corpus_root> ...]``
    Resolves every row's anchor against the given corpus roots and prints
    the report as JSON. Exit code is always ``0`` (invocation errors
    aside) — this tool is advisory; the calling critic decides how to
    weigh a ``DRIFTED``/``NOT_FOUND`` row.

``python -m anvil.lib.provenance_anchor repoint <provenance.md> <corpus_root> [<corpus_root> ...]``
    Mechanically rewrites the ``Line range`` cell of every
    :data:`STATUS_DRIFTED` row to the anchor's resolved current location.
    Leaves every other cell, and every non-drifted row, byte-identical.
    Prints a summary of what was repointed as JSON. Atomic via the
    shared :func:`anvil.lib.atomic_write.atomic_write_text` helper.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from anvil.lib.atomic_write import atomic_write_text

# ---------------------------------------------------------------------------
# Status vocabulary
# ---------------------------------------------------------------------------

STATUS_NO_ANCHOR = "NO_ANCHOR"
"""The row has no ``Anchor`` cell value (legacy row predating this
feature, or an unmigrated row) — drift detection unavailable. Never a
drift signal, never an error."""

STATUS_FILE_NOT_FOUND = "FILE_NOT_FOUND"
"""``Source file`` does not resolve under any given corpus root."""

STATUS_NOT_FOUND = "NOT_FOUND"
"""The anchor text is not present anywhere in the resolved source file —
the passage was deleted or rewritten, not merely moved. Degrades to the
five-way vocabulary's ``NOT_FOUND`` classification, NOT a drift finding
(edge case (a) from issue #868's test plan)."""

STATUS_RESOLVED = "RESOLVED"
"""The anchor text is present and its location overlaps the cited
``Line range`` hint (or the row has no parseable hint to compare
against) — no drift."""

STATUS_DRIFTED = "DRIFTED"
"""The anchor text is present verbatim in the source file but at a
location that does NOT overlap the cited ``Line range`` hint — the hint
is stale, the citation itself is not. Distinct from
:data:`STATUS_NOT_FOUND` / a content mismatch classification."""

_STATUSES = (
    STATUS_NO_ANCHOR,
    STATUS_FILE_NOT_FOUND,
    STATUS_NOT_FOUND,
    STATUS_RESOLVED,
    STATUS_DRIFTED,
)

_CURLY_FOLD = {
    "“": '"',
    "”": '"',
    "‘": "'",
    "’": "'",
}


def normalize(text: str) -> str:
    """Fold curly quotes to straight and collapse whitespace runs.

    Case-sensitive by contract — an anchor is a verbatim quote or it is
    not evidence, the same posture as ``evidence_check.py::normalize``.
    """
    for curly, straight in _CURLY_FOLD.items():
        text = text.replace(curly, straight)
    return " ".join(text.split())


# ---------------------------------------------------------------------------
# provenance.md table parsing
# ---------------------------------------------------------------------------

_LINE_RANGE_RE = re.compile(r"(\d+)\s*(?:-\s*(\d+))?")


def _parse_line_ranges(cell: str) -> List[Tuple[int, int]]:
    """Parse a ``Line range`` cell that MAY hold several comma-separated
    ranges (``"61-63, 1, 37-39"``), returning every one that parses, in
    cell order — not just the first.

    Each comma-separated fragment is parsed independently, so a single
    malformed fragment (a stray trailing comma producing an empty
    fragment, stray non-numeric text) is silently skipped rather than
    discarding the whole cell or raising. A cell with no parseable
    fragment at all (``"?"``, ``"NOT_FOUND"``, empty) returns ``[]`` — a
    row with no usable hint, not an error.
    """
    ranges: List[Tuple[int, int]] = []
    for fragment in (cell or "").split(","):
        m = _LINE_RANGE_RE.search(fragment)
        if not m:
            continue
        start = int(m.group(1))
        end = int(m.group(2)) if m.group(2) else start
        if end < start:
            start, end = end, start
        ranges.append((start, end))
    return ranges


def _parse_line_range(cell: str) -> Optional[Tuple[int, int]]:
    """Parse a ``Line range`` cell and return its FIRST range only
    (``"412-415"``, ``"7"``, ``"L412-415"``) — kept for callers that only
    care about a single primary hint (e.g. :attr:`ProvenanceRow.line_range`).
    See :func:`_parse_line_ranges` for the full comma-separated list.

    Returns ``None`` for anything unparsable (``"?"``, ``"NOT_FOUND"``,
    empty) — a row with no usable hint, not an error.
    """
    ranges = _parse_line_ranges(cell)
    return ranges[0] if ranges else None


def _split_row(line: str) -> List[str]:
    """Split a ``| a | b | c |`` markdown table row into stripped cells."""
    stripped = line.strip()
    if stripped.startswith("|"):
        stripped = stripped[1:]
    if stripped.endswith("|"):
        stripped = stripped[:-1]
    return [cell.strip() for cell in stripped.split("|")]


def _is_separator_row(cells: Sequence[str]) -> bool:
    return bool(cells) and all(re.fullmatch(r":?-{2,}:?", c.strip()) for c in cells)


def _find_col(lowered_header: Sequence[str], *names: str) -> Optional[int]:
    for i, cell in enumerate(lowered_header):
        if any(name in cell for name in names):
            return i
    return None


@dataclass
class ProvenanceRow:
    """One parsed ``provenance.md`` table row."""

    line_no: int
    """1-based line number of this row within ``provenance.md`` (for
    ``evidence_span``-style back-references, e.g. ``provenance.md:L<N>``)."""

    claim: str
    source_file: str
    line_range_raw: str
    line_range: Optional[Tuple[int, int]]
    """The cell's FIRST parsed range only — kept for backward
    compatibility with callers that assume a single hint. See
    :attr:`line_range_hints` for the full comma-separated list."""

    anchor: Optional[str]
    """``None`` when the row has no ``Anchor`` column value at all — a
    legacy (pre-#868) row or unmigrated table shape."""

    notes: str

    table_index: int = 0
    """0-based index into :attr:`ParsedProvenanceTable.tables` identifying
    which conforming table this row came from — a ``provenance.md`` file
    may hold several (issue #934)."""

    line_range_col: Optional[int] = None
    """The ``Line range`` column index *within this row's own table* —
    tables may be laid out with different column orders, so this is not
    necessarily the same value across every row in the file."""

    anchor_col: Optional[int] = None
    """The ``Anchor`` column index within this row's own table, or
    ``None`` if that table has no ``Anchor`` column at all."""

    line_range_hints: List[Tuple[int, int]] = field(default_factory=list)
    """EVERY range parsed from the ``Line range`` cell, in cell order
    (issue #1204) — a cell MAY cite several comma-separated ranges
    (``"61-63, 1, 37-39"``). Empty when the cell has no parseable range
    at all (mirrors :attr:`line_range` being ``None`` in that case).
    :func:`resolve_anchor` treats a row RESOLVED if the anchor overlaps
    ANY of these, not just the first."""


@dataclass
class TableInfo:
    """One conforming (``Claim`` + ``Source file`` header) claim table
    found in a ``provenance.md`` file."""

    header_line: int
    """1-based line number of this table's header row."""

    header: List[str]
    line_range_col: Optional[int]
    anchor_col: Optional[int]


@dataclass
class SkippedTableInfo:
    """A markdown table (header + separator row) found in a
    ``provenance.md`` file that was NOT recognized as a claim table (no
    header cell matched ``Claim``/``Source``) — its rows are excluded
    from parsing, but the table's existence is reported rather than
    silently dropped (issue #934 acceptance criterion)."""

    header_line: int
    """1-based line number of the skipped table's header row."""

    header: List[str]
    reason: str

    def to_json(self) -> Dict[str, Any]:
        return {
            "header_line": self.header_line,
            "header": self.header,
            "reason": self.reason,
        }


@dataclass
class ParsedProvenanceTable:
    """A parsed ``provenance.md`` file: every conforming claim table's
    rows (flattened, in file order) + the raw lines (kept for
    :func:`repoint_drifted_anchors` to rewrite in place).

    ``header`` / ``line_range_col`` / ``anchor_col`` describe the FIRST
    conforming table only (kept for backward compatibility with single-
    table callers/tests); use :attr:`tables` for the full per-table
    picture on a multi-table file.
    """

    header: List[str]
    line_range_col: Optional[int]
    anchor_col: Optional[int]
    rows: List[ProvenanceRow]
    lines: List[str]
    tables: List[TableInfo] = field(default_factory=list)
    skipped_tables: List[SkippedTableInfo] = field(default_factory=list)


def parse_provenance_table(path: Path) -> ParsedProvenanceTable:
    """Parse a ``provenance.md`` claim->source map.

    Tolerates both the legacy 4-column shape (``Claim | Source file |
    Line range | Notes``) and the anchor-bearing 5-column shape
    (``Claim | Source file | Line range | Anchor | Notes``) — column
    identity is derived from each table's own header row, not a fixed
    position, so either shape (or a consumer-reordered variant) parses
    correctly. Rows in a legacy table (no ``Anchor`` header) get
    ``anchor=None`` (:data:`STATUS_NO_ANCHOR`) rather than raising.

    A single file MAY contain several independent claim tables (e.g. one
    per chapter in a memoir book) — every conforming table's rows are
    returned, not just the first (issue #934). A blank line, a heading,
    or simply the next table's header immediately following the last
    row (no blank line required) all correctly end the current table.
    Markdown tables that are NOT claim tables (no ``Claim``/``Source``
    header) are recognized as tables but excluded from ``rows`` — they
    are reported via :attr:`ParsedProvenanceTable.skipped_tables` rather
    than silently dropped.
    """
    lines = Path(path).read_text(encoding="utf-8").splitlines()
    n = len(lines)

    rows: List[ProvenanceRow] = []
    tables: List[TableInfo] = []
    skipped_tables: List[SkippedTableInfo] = []

    # `active` is the TableInfo we are currently collecting rows for, or
    # None when we are not positioned inside a recognized claim table
    # (before the first header, between tables, or inside a skipped
    # non-conforming table).
    active: Optional[TableInfo] = None

    idx = 0
    while idx < n:
        line = lines[idx]
        if not line.strip().startswith("|"):
            active = None
            idx += 1
            continue

        cells = _split_row(line)
        next_line = lines[idx + 1] if idx + 1 < n else ""
        next_is_separator = next_line.strip().startswith("|") and _is_separator_row(
            _split_row(next_line)
        )

        if next_is_separator:
            # This line + the next together form a NEW table's header +
            # separator row — true whether or not we were already inside
            # another table (adjacent tables with no blank line between
            # them are handled identically to blank-line-separated ones).
            lowered = [c.lower() for c in cells]
            if "claim" in lowered and any("source" in c for c in lowered):
                line_range_col = _find_col(lowered, "line range", "line-range")
                anchor_col = _find_col(lowered, "anchor")
                active = TableInfo(
                    header_line=idx + 1,
                    header=cells,
                    line_range_col=line_range_col,
                    anchor_col=anchor_col,
                )
                tables.append(active)
            else:
                active = None
                skipped_tables.append(
                    SkippedTableInfo(
                        header_line=idx + 1,
                        header=cells,
                        reason=(
                            "header row has no recognizable Claim/Source "
                            "columns — table skipped, not parsed as claim "
                            "rows."
                        ),
                    )
                )
            idx += 2  # consume header row + separator row
            continue

        if active is None:
            # A stray pipe-containing line outside any recognized table
            # context (or inside a just-skipped non-conforming table).
            idx += 1
            continue

        if _is_separator_row(cells):
            idx += 1
            continue
        if len(cells) < 2:
            idx += 1
            continue

        lowered_header = [c.lower() for c in active.header]
        claim_col = _find_col(lowered_header, "claim")
        source_col = _find_col(lowered_header, "source")
        notes_col = _find_col(lowered_header, "notes")

        def _cell(col: Optional[int]) -> str:
            if col is None or col >= len(cells):
                return ""
            return cells[col]

        claim = _cell(claim_col)
        source_file = _cell(source_col)
        line_range_raw = _cell(active.line_range_col)
        line_range_hints = _parse_line_ranges(line_range_raw)
        notes = _cell(notes_col)
        anchor_cell = _cell(active.anchor_col) if active.anchor_col is not None else None
        anchor = anchor_cell.strip("\"'“” ") if anchor_cell else None
        if anchor is not None and not anchor:
            anchor = None

        rows.append(
            ProvenanceRow(
                line_no=idx + 1,
                claim=claim,
                source_file=source_file,
                line_range_raw=line_range_raw,
                line_range=line_range_hints[0] if line_range_hints else None,
                anchor=anchor,
                notes=notes,
                table_index=len(tables) - 1,
                line_range_col=active.line_range_col,
                anchor_col=active.anchor_col,
                line_range_hints=line_range_hints,
            )
        )
        idx += 1

    first = tables[0] if tables else None
    return ParsedProvenanceTable(
        header=first.header if first else [],
        line_range_col=first.line_range_col if first else None,
        anchor_col=first.anchor_col if first else None,
        rows=rows,
        lines=lines,
        tables=tables,
        skipped_tables=skipped_tables,
    )


# ---------------------------------------------------------------------------
# Corpus file resolution
# ---------------------------------------------------------------------------


def resolve_source_file(
    source_file: str, corpus_roots: Sequence[Path]
) -> Optional[Path]:
    """Resolve ``source_file`` (a path relative to a declared corpus dir)
    against the given ``corpus_roots``, in order. ``None`` if it
    resolves under none of them (:data:`STATUS_FILE_NOT_FOUND`)."""
    for root in corpus_roots:
        candidate = Path(root) / source_file
        if candidate.is_file():
            return candidate
    return None


# ---------------------------------------------------------------------------
# Anchor resolution
# ---------------------------------------------------------------------------


def _normalize_with_line_map(text: str) -> Tuple[str, List[int]]:
    """Normalize ``text`` the way :func:`normalize` does, but also return
    a parallel list mapping each output character's index back to its
    1-based source line number — needed to translate a match position
    back into a citable line range."""
    out_chars: List[str] = []
    out_lines: List[int] = []
    lineno = 1
    pending_space = False
    started = False
    for ch in text:
        if ch == "\n":
            lineno += 1
            pending_space = True
            continue
        folded = _CURLY_FOLD.get(ch, ch)
        if folded.isspace():
            pending_space = True
            continue
        if pending_space and started:
            out_chars.append(" ")
            out_lines.append(lineno)
        pending_space = False
        started = True
        out_chars.append(folded)
        out_lines.append(lineno)
    return "".join(out_chars), out_lines


def _find_all(haystack: str, needle: str) -> List[int]:
    if not needle:
        return []
    idxs: List[int] = []
    start = 0
    while True:
        idx = haystack.find(needle, start)
        if idx == -1:
            break
        idxs.append(idx)
        start = idx + 1
    return idxs


def _ranges_overlap(a: Tuple[int, int], b: Tuple[int, int]) -> bool:
    return a[0] <= b[1] and b[0] <= a[1]


@dataclass
class AnchorResolution:
    """Outcome of resolving one :class:`ProvenanceRow`'s anchor."""

    row: ProvenanceRow
    status: str
    resolved_range: Optional[Tuple[int, int]]
    occurrences: int
    detail: str

    @property
    def drifted(self) -> bool:
        return self.status == STATUS_DRIFTED

    def to_json(self) -> Dict[str, Any]:
        return {
            "row_line": self.row.line_no,
            "claim": self.row.claim,
            "source_file": self.row.source_file,
            "line_range_hint": list(self.row.line_range)
            if self.row.line_range
            else None,
            "line_range_hints": [list(h) for h in self.row.line_range_hints],
            "anchor": self.row.anchor,
            "status": self.status,
            "resolved_range": list(self.resolved_range)
            if self.resolved_range
            else None,
            "occurrences": self.occurrences,
            "detail": self.detail,
        }


def resolve_anchor(
    file_path: Optional[Path], row: ProvenanceRow
) -> AnchorResolution:
    """Resolve one row's anchor against ``file_path`` (already resolved
    via :func:`resolve_source_file`; ``None`` means unresolvable)."""
    if not row.anchor:
        return AnchorResolution(
            row=row,
            status=STATUS_NO_ANCHOR,
            resolved_range=None,
            occurrences=0,
            detail=(
                "row has no Anchor column value (legacy row predating "
                "issue #868, or not yet migrated) — anchor-drift "
                "detection is unavailable for this row until the next "
                "draft/revise pass adds one."
            ),
        )

    if file_path is None:
        return AnchorResolution(
            row=row,
            status=STATUS_FILE_NOT_FOUND,
            resolved_range=None,
            occurrences=0,
            detail=(
                f"source file '{row.source_file}' is not resolvable "
                "under any declared corpus root."
            ),
        )

    normalized_anchor = normalize(row.anchor)
    if not normalized_anchor:
        return AnchorResolution(
            row=row,
            status=STATUS_NO_ANCHOR,
            resolved_range=None,
            occurrences=0,
            detail="row's Anchor cell is empty after normalization.",
        )

    text = file_path.read_text(encoding="utf-8", errors="replace")
    normalized_text, line_map = _normalize_with_line_map(text)
    idxs = _find_all(normalized_text, normalized_anchor)

    if not idxs:
        return AnchorResolution(
            row=row,
            status=STATUS_NOT_FOUND,
            resolved_range=None,
            occurrences=0,
            detail=(
                f"anchor text not found anywhere in '{row.source_file}' "
                "— the passage was deleted or rewritten, not merely "
                "moved (degrades to the five-way NOT_FOUND "
                "classification, not a drift finding)."
            ),
        )

    candidates: List[Tuple[int, int]] = []
    for idx in idxs:
        start_line = line_map[idx]
        end_idx = min(idx + len(normalized_anchor) - 1, len(line_map) - 1)
        end_line = line_map[end_idx]
        candidates.append((start_line, end_line))

    # A Line range cell MAY hold several comma-separated ranges (issue
    # #1204, e.g. "61-63, 1, 37-39") — `hints` is EVERY range parsed from
    # the cell, in cell order. The overlap check and the nearest-candidate
    # tie-break below both consider every hint, not just the first, so
    # the anchor's true location can be corroborated by ANY cited range.
    hints = row.line_range_hints

    def _nearest_hint_distance(candidate: Tuple[int, int]) -> int:
        # Nearest to the CLOSEST of all hint ranges — a single-hint cell
        # reduces to the pre-#1204 "nearest to the hint" rule exactly
        # (test_coincidental_duplicate_resolves_to_nearest_hint), and a
        # multi-hint cell extends it the obvious way: a candidate that is
        # close to any one cited range is treated as close overall.
        return min(abs(candidate[0] - h[0]) for h in hints)

    if hints:
        chosen = min(candidates, key=_nearest_hint_distance)
    else:
        chosen = candidates[0]

    ambiguous_note = ""
    if len(candidates) > 1:
        ambiguous_note = (
            f" ({len(candidates)} occurrences found in the file; resolved "
            "to the one nearest the cited Line range hint.)"
        )

    if not hints:
        return AnchorResolution(
            row=row,
            status=STATUS_RESOLVED,
            resolved_range=chosen,
            occurrences=len(candidates),
            detail=(
                f"anchor resolved to '{row.source_file}':{chosen[0]}-"
                f"{chosen[1]}; row has no parseable Line range hint to "
                "compare against." + ambiguous_note
            ),
        )

    hints_str = ", ".join(_format_line_range(h) for h in hints)

    if any(_ranges_overlap(chosen, h) for h in hints):
        return AnchorResolution(
            row=row,
            status=STATUS_RESOLVED,
            resolved_range=chosen,
            occurrences=len(candidates),
            detail=(
                f"anchor found at '{row.source_file}':{chosen[0]}-"
                f"{chosen[1]}, matching the cited hint(s) "
                f"{hints_str}." + ambiguous_note
            ),
        )

    return AnchorResolution(
        row=row,
        status=STATUS_DRIFTED,
        resolved_range=chosen,
        occurrences=len(candidates),
        detail=(
            f"anchor text is still present verbatim in "
            f"'{row.source_file}' but now at line {chosen[0]}-{chosen[1]} "
            f"(row cites {hints_str}) — the Line range hint is "
            "stale, not the claim. Distinct from a content MISMATCH: the "
            "cited passage was found, just not where the row says it "
            "is." + ambiguous_note
        ),
    )


# ---------------------------------------------------------------------------
# Whole-table check
# ---------------------------------------------------------------------------


def check_provenance_anchors(
    provenance_path: Path, corpus_roots: Sequence[Path]
) -> Dict[str, Any]:
    """Resolve every row of ``provenance_path`` against ``corpus_roots``.

    A ``provenance.md`` file may hold several independent claim tables
    (issue #934) — ``total_rows`` and ``anchor_column_present`` describe
    the WHOLE FILE (aggregated across every conforming table found), not
    just the first. ``table_count`` reports how many conforming tables
    were found, and ``skipped_tables`` reports any markdown table that
    was recognized but excluded for lacking Claim/Source columns, so a
    non-conforming table is never silently dropped from the report.

    Returns a JSON-serializable report: per-row resolutions plus summary
    counts across the five statuses. Never raises for a missing/empty
    provenance file — an empty table reports zero rows.
    """
    table = parse_provenance_table(provenance_path)
    counts: Dict[str, int] = {status: 0 for status in _STATUSES}
    resolutions: List[AnchorResolution] = []

    for row in table.rows:
        file_path = resolve_source_file(row.source_file, corpus_roots)
        resolution = resolve_anchor(file_path, row)
        resolutions.append(resolution)
        counts[resolution.status] += 1

    return {
        "provenance_path": str(provenance_path),
        "total_rows": len(table.rows),
        "table_count": len(table.tables),
        "anchor_column_present": any(t.anchor_col is not None for t in table.tables),
        "skipped_tables": [t.to_json() for t in table.skipped_tables],
        "counts": counts,
        "drifted": counts[STATUS_DRIFTED] > 0,
        "rows": [r.to_json() for r in resolutions],
    }


# ---------------------------------------------------------------------------
# Mechanical repoint
# ---------------------------------------------------------------------------


def _format_line_range(rng: Tuple[int, int]) -> str:
    start, end = rng
    return str(start) if start == end else f"{start}-{end}"


def _rewrite_line_range_cell(line: str, col_index: int, new_value: str) -> str:
    """Rewrite the ``col_index``-th cell of a markdown table row to
    ``new_value``, preserving every other cell and the row's leading/
    trailing pipe style."""
    stripped = line.strip()
    leading = "|" if stripped.startswith("|") else ""
    trailing = "|" if stripped.endswith("|") else ""
    body = stripped
    if leading:
        body = body[1:]
    if trailing and body.endswith("|"):
        body = body[:-1]
    cells = body.split("|")
    if col_index >= len(cells):
        return line
    cells[col_index] = f" {new_value} "
    return leading + "|".join(cells) + trailing


def repoint_drifted_anchors(
    provenance_path: Path, corpus_roots: Sequence[Path]
) -> Dict[str, Any]:
    """Mechanically rewrite the ``Line range`` cell of every
    :data:`STATUS_DRIFTED` row to its anchor's resolved current location,
    across EVERY conforming claim table in the file (issue #934) — not
    just the first.

    Only :data:`STATUS_DRIFTED` rows are touched; every other row (and
    every non-table line — prose, headings) is written back byte-
    identical. Each row is repointed using its OWN table's column
    layout (``row.line_range_col`` / ``row.anchor_col``), so tables with
    different column orders in the same file are each handled correctly.
    A no-op (returns ``repointed: []``) when no table in the file has
    both a ``Line range`` and an ``Anchor`` column, when there are no
    rows, or when nothing is drifted. Any non-conforming table found in
    the file is reported via ``skipped_tables`` — this function never
    reports success while silently having examined only some of the
    file's tables. Atomic write via tmp-then-``os.replace``.

    Multi-range hints (issue #1204): a cell MAY cite several
    comma-separated ranges (``"61-63, 1, 37-39"``). After the #1204 fix,
    :func:`resolve_anchor` only classifies a row :data:`STATUS_DRIFTED`
    when the anchor's true location overlaps NONE of the cell's cited
    ranges — i.e. every range the row currently cites is equally stale.
    There is therefore no "still-good" cited range worth preserving in
    that case, so this function deliberately COLLAPSES the whole cell to
    the anchor's single resolved location rather than appending it
    alongside the old (now-known-wrong) ranges — carrying stale ranges
    forward would misinform the next reader exactly as the original bug
    did. A row whose anchor overlaps at least one cited range is
    RESOLVED, not DRIFTED, and is never touched here, so a genuinely
    still-good range in a multi-range cell is never at risk of being
    dropped.
    """
    table = parse_provenance_table(provenance_path)
    repointed: List[Dict[str, Any]] = []
    skipped_tables_json = [t.to_json() for t in table.skipped_tables]

    repointable_tables = [
        t for t in table.tables if t.line_range_col is not None and t.anchor_col is not None
    ]

    if not repointable_tables:
        return {
            "provenance_path": str(provenance_path),
            "repointed": repointed,
            "table_count": len(table.tables),
            "skipped_tables": skipped_tables_json,
            "detail": (
                "no table in this file has both a Line range and an "
                "Anchor column — nothing to mechanically repoint."
            ),
        }

    new_lines = list(table.lines)
    for row in table.rows:
        if row.line_range_col is None or row.anchor_col is None:
            # This row's own table has no Anchor and/or Line range
            # column — never a candidate for repointing.
            continue
        file_path = resolve_source_file(row.source_file, corpus_roots)
        resolution = resolve_anchor(file_path, row)
        if resolution.status != STATUS_DRIFTED or resolution.resolved_range is None:
            continue
        idx = row.line_no - 1
        new_value = _format_line_range(resolution.resolved_range)
        new_lines[idx] = _rewrite_line_range_cell(
            new_lines[idx], row.line_range_col, new_value
        )
        repointed.append(
            {
                "row_line": row.line_no,
                "table_index": row.table_index,
                "claim": row.claim,
                "source_file": row.source_file,
                "old_line_range": row.line_range_raw,
                "new_line_range": new_value,
            }
        )

    if repointed:
        atomic_write_text(
            Path(provenance_path), "\n".join(new_lines) + "\n"
        )

    detail = (
        f"mechanically repointed {len(repointed)} drifted row(s) across "
        f"{len(table.tables)} claim table(s) in this file; Claim/Source "
        "file/Anchor/Notes left untouched."
        if repointed
        else "no drifted rows found — nothing repointed."
    )
    if table.skipped_tables:
        detail += (
            f" WARNING: {len(table.skipped_tables)} table(s) in this file "
            "were not recognized as claim tables (no Claim/Source header) "
            "and were NOT examined — see 'skipped_tables'."
        )

    return {
        "provenance_path": str(provenance_path),
        "repointed": repointed,
        "table_count": len(table.tables),
        "skipped_tables": skipped_tables_json,
        "detail": detail,
    }


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.provenance_anchor",
        description=(
            "Deterministic provenance.md anchor-drift advisory (issue "
            "#868). 'check' reports drift; 'repoint' mechanically fixes "
            "the Line range hint of drifted rows."
        ),
    )
    sub = p.add_subparsers(dest="command", required=True)

    check_p = sub.add_parser(
        "check",
        help="Resolve every row's anchor and report drift status as JSON.",
    )
    check_p.add_argument("provenance_path", help="Path to provenance.md.")
    check_p.add_argument(
        "corpus_roots", nargs="+", help="One or more resolved corpus root dirs."
    )

    repoint_p = sub.add_parser(
        "repoint",
        help="Mechanically rewrite drifted rows' Line range cell in place.",
    )
    repoint_p.add_argument("provenance_path", help="Path to provenance.md.")
    repoint_p.add_argument(
        "corpus_roots", nargs="+", help="One or more resolved corpus root dirs."
    )

    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Always exits ``0`` on a successful invocation of
    either subcommand (both are advisory/mechanical, never a pass/fail
    gate); ``2`` on an invocation error."""
    parser = _build_cli_parser()
    args = parser.parse_args(argv)

    try:
        corpus_roots = [Path(r) for r in args.corpus_roots]
        if args.command == "check":
            report = check_provenance_anchors(Path(args.provenance_path), corpus_roots)
            print(json.dumps(report, indent=2))
            return 0
        if args.command == "repoint":
            report = repoint_drifted_anchors(Path(args.provenance_path), corpus_roots)
            print(json.dumps(report, indent=2))
            return 0
    except OSError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    return 2  # pragma: no cover - argparse enforces a valid subcommand


__all__ = [
    "STATUS_NO_ANCHOR",
    "STATUS_FILE_NOT_FOUND",
    "STATUS_NOT_FOUND",
    "STATUS_RESOLVED",
    "STATUS_DRIFTED",
    "normalize",
    "ProvenanceRow",
    "TableInfo",
    "SkippedTableInfo",
    "ParsedProvenanceTable",
    "parse_provenance_table",
    "resolve_source_file",
    "AnchorResolution",
    "resolve_anchor",
    "check_provenance_anchors",
    "repoint_drifted_anchors",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
