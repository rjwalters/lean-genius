"""Deterministic float-proximity pre-flight (issue #1398).

Seventh member of the deterministic-checks family (alongside
``anvil/lib/audience_check.py``, ``anvil/lib/numeric_consistency.py``,
``anvil/lib/pending_marker.py`` and ``anvil/lib/render_gate/``). Child of
#1396, class 4.

The problem
-----------

A float (figure or table) can render pages away from, or in a different
section than, the prose that first cites it: Table 1 six pages before its
primer, Fig. 3 in section 6 with its text in section 5. Nothing in the
compile gate notices, because the document compiles cleanly.

Data source (stated per the acceptance criteria)
------------------------------------------------

The compiled artifacts of the version directory, no VLM:

- ``<stem>.aux`` -- float inventory and printed page, from the
  ``\\contentsline {figure|table}{\\numberline {N}...}{page}`` entries LaTeX
  writes into the ``lof``/``lot`` lists; section start pages, from the
  ``\\contentsline {section}{\\numberline {S}...}{page}`` entries written
  into the ``toc`` list.
- ``<stem>.pdf`` via ``pdftotext`` -- the page where each float's caption
  renders, and the page of its first in-text mention.

Chosen over label-based ``\\newlabel`` data because the lof/lot entries
exist for every captioned float. The page is the first ``}{<digits>}`` after
the number, so the trailing ``{label}`` group ``hyperref`` appends is neither
required nor captured (a lazy match keeps it from being read as the page).

Heuristic and its limits
------------------------

The first-reference page is the first PDF page holding ``Figure N`` /
``Fig. N`` / ``Table N`` (case-insensitive) that is not a caption line (a
line that starts with the label followed by ``:``, ``.`` or ``|``). This is
a string match, not a parse of the ``\\ref``: a mention that wraps across a
line break is missed, "Figure 3" quoted in running text of an unrelated
chapter is a false match, and a caption that begins ``Figure 3 shows ...``
without punctuation reads as a mention. A float whose caption or mention
cannot be located is listed under ``unmatched`` and never reported. Only
the FIRST reference is considered. Printed page numbers are mapped to PDF
page indexes with the offset observed between each float's aux page and its
caption page in the PDF (the most common offset wins), so front matter with
roman numbering does not shift results. Floats whose section is an appendix
are skipped (an appendix float cited from the body is far away by design).
A float's section is the section its ``\\caption`` is written in: the last
``section`` entry that precedes the float's ``lof``/``lot`` entry in the
``.aux`` (LaTeX writes the entries in source order), falling back to the
last section starting on or before its page when none precedes it. The
reference side is still page-based (the ``.aux`` does not record where a
mention sits), so a mention on a page where a section begins mid-page can
still read as a cross-section hit.

A mention is not counted as the first reference when it sits inside another
float: on a page that also carries a different float's caption, a mention in
that caption's paragraph, or in a paragraph made only of short lines (a
table or glossary cell as ``pdftotext`` emits it), is skipped. This is a
text-shape guess, not a layout parse; a very short prose paragraph on such a
page can be skipped by mistake. A line-initial ``Table N.`` counts as the
caption only on the caption's page, so the tail of a wrapped sentence
elsewhere is a mention; when several lines look like the caption, the one on
the page nearest ``aux_page + offset`` wins.

Posture: ADVISORY, fail-open
----------------------------

Like ``audience_check``: ``kind: tool_evidence``, findings at ``minor``
(warning), no critical flag, ``score=None``. When no ``.aux``, no ``.pdf``
or no ``pdftotext`` is available the check records a stated note and
reports nothing.

Writes ``<version_dir>.floats/_review.json`` through
``anvil/lib/sidecar.py::write_critic_review_dir`` (``staged_sidecar``).
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from anvil.lib.body_resolution import resolve_body_path
from anvil.lib.render_gate.probes import _extract_pdf_text
from anvil.lib.review_schema import Finding, Kind, Review, Score
from anvil.lib.sidecar import write_critic_review_dir

CRITIC_ID = "floats"
CHECK_NAME = "float_proximity"
DIM_FLOAT = "reader_flow"
FLOATS_SUFFIX = "floats"
MAX_PAGE_GAP = 1

REASON_NO_AUX = "no .aux file found next to the body"
REASON_NO_PDF = "no compiled .pdf found next to the body"
REASON_NO_TEXT = "pdftotext unavailable or failed on the PDF"
REASON_NO_FLOATS = "no captioned floats in the .aux"

_CONTENTSLINE = re.compile(
    r"\\contentsline\s*\{(?P<kind>figure|table|section)\}"
    r"\{\\numberline\s*\{(?P<num>[^{}]*)\}.*?\}\{(?P<page>\d+)\}"
)


@dataclass(frozen=True)
class FloatEntry:
    kind: str  # "figure" | "table"
    number: str
    aux_page: int
    section: Optional[str] = None  # section whose text wrote this caption (.aux order)

    @property
    def name(self) -> str:
        return f"{'Figure' if self.kind == 'figure' else 'Table'} {self.number}"


@dataclass(frozen=True)
class FloatHit:
    name: str
    float_page: int
    ref_page: int
    float_section: Optional[str]
    ref_section: Optional[str]
    reasons: Tuple[str, ...]

    def to_dict(self) -> dict:
        return {
            "float": self.name,
            "float_page": self.float_page,
            "first_ref_page": self.ref_page,
            "float_section": self.float_section,
            "first_ref_section": self.ref_section,
            "reasons": list(self.reasons),
        }


def parse_aux(aux_text: str) -> Tuple[List[FloatEntry], List[Tuple[str, int]]]:
    """Return ``(floats, sections)`` from ``.aux`` text.

    ``sections`` is ``[(number, printed_page)]`` in document order. Entries
    whose page is not an arabic integer are dropped.
    """
    floats: List[FloatEntry] = []
    sections: List[Tuple[str, int]] = []
    seen = set()
    current_section: Optional[str] = None
    for m in _CONTENTSLINE.finditer(aux_text):
        page = m.group("page").strip()
        if not page.isdigit():
            continue
        kind, num = m.group("kind"), m.group("num").strip()
        if kind == "section":
            sections.append((num, int(page)))
            current_section = num
        elif (kind, num) not in seen:
            seen.add((kind, num))
            floats.append(FloatEntry(kind, num, int(page), current_section))
    return floats, sections


def _label_pattern(entry: FloatEntry) -> "re.Pattern[str]":
    word = r"(?:Figure|Fig\.?)" if entry.kind == "figure" else r"Table"
    return re.compile(rf"\b{word}\s*{re.escape(entry.number)}(?![\w.]*\d)", re.IGNORECASE)


_CAPTION_PUNCT = (":", ".", "|")
_SHORT_LINE = 50  # pdftotext lines of table/glossary cells are short; prose runs wider


def _caption_pages(entry: FloatEntry, pages: Sequence[str]) -> List[int]:
    """Every page holding a caption-like line for ``entry`` (1-based, ascending)."""
    pat = _label_pattern(entry)
    found: List[int] = []
    for idx, text in enumerate(pages, start=1):
        for line in text.splitlines():
            m = pat.match(line.strip())
            if m and line.strip()[m.end():m.end() + 1] in _CAPTION_PUNCT:
                found.append(idx)
                break
    return found


def _resolve_captions(
    floats: Sequence[FloatEntry], pages: Sequence[str]
) -> Tuple[Dict[FloatEntry, int], List[str], int]:
    """Return ``(caption page per float, unmatched names, aux->pdf page offset)``.

    Floats with exactly one caption-like page fix the offset; ambiguous ones
    (a wrapped sentence ending ``... Table 5.`` also looks like a caption)
    then take the candidate nearest ``aux_page + offset``.
    """
    candidates = {f: _caption_pages(f, pages) for f in floats}
    unmatched = [f.name for f, c in candidates.items() if not c]
    sure = {f: c[0] for f, c in candidates.items() if len(c) == 1}
    basis = sure or {f: c[0] for f, c in candidates.items() if c}
    offsets = Counter(page - f.aux_page for f, page in basis.items())
    offset = offsets.most_common(1)[0][0] if offsets else 0
    captions: Dict[FloatEntry, int] = {}
    for f, c in candidates.items():
        if c:
            captions[f] = min(c, key=lambda p: (abs(p - (f.aux_page + offset)), p))
    return captions, unmatched, offset


def _in_other_float(lines: Sequence[str], at: int, caption_lines: Sequence[int]) -> bool:
    """Is ``lines[at]`` part of a paragraph that is another float's caption or body?

    ``caption_lines`` are indexes of other floats' caption lines on this page.
    """
    lo = at
    while lo > 0 and lines[lo - 1].strip():
        lo -= 1
    hi = at
    while hi + 1 < len(lines) and lines[hi + 1].strip():
        hi += 1
    if any(lo <= c <= hi for c in caption_lines):
        return True
    return all(len(lines[k].strip()) <= _SHORT_LINE for k in range(lo, hi + 1))


def _first_ref_page(
    entry: FloatEntry,
    pages: Sequence[str],
    caption_page: Optional[int] = None,
    other_captions: Optional[Dict[int, List[int]]] = None,
) -> Optional[int]:
    """First page with a real mention; see the module docstring for what is skipped.

    ``other_captions`` maps a 1-based page to the line indexes of *other*
    floats' captions there (precomputed by :func:`analyze`).
    """
    pat = _label_pattern(entry)
    for idx, text in enumerate(pages, start=1):
        lines = text.splitlines()
        foreign = (other_captions or {}).get(idx, [])
        for at, line in enumerate(lines):
            stripped = line.strip()
            for m in pat.finditer(stripped):
                punct = stripped[m.end():m.end() + 1] in _CAPTION_PUNCT
                if m.start() == 0 and punct and (caption_page is None or idx == caption_page):
                    continue
                if foreign and _in_other_float(lines, at, foreign):
                    continue
                return idx
    return None


def _caption_line_index(entry: FloatEntry, lines: Sequence[str]) -> Optional[int]:
    pat = _label_pattern(entry)
    for at, line in enumerate(lines):
        m = pat.match(line.strip())
        if m and line.strip()[m.end():m.end() + 1] in _CAPTION_PUNCT:
            return at
    return None


def _is_appendix(section_number: Optional[str]) -> bool:
    return bool(section_number) and section_number[:1].isalpha()


def _section_at(page: int, sections: Sequence[Tuple[str, int]]) -> Optional[str]:
    current = None
    for num, start in sections:
        if start <= page:
            current = num
    return current


def analyze(
    aux_text: str,
    pages: Sequence[str],
    *,
    max_gap: int = MAX_PAGE_GAP,
) -> Tuple[List[FloatHit], List[str]]:
    """Pure core: ``(hits, unmatched)`` from aux text and per-page PDF text."""
    floats, sections = parse_aux(aux_text)
    captions, unmatched, offset = _resolve_captions(floats, pages)
    pdf_sections = [(num, start + offset) for num, start in sections]
    caption_lines: Dict[FloatEntry, Dict[int, List[int]]] = {}
    for f, cpage in captions.items():
        at = _caption_line_index(f, pages[cpage - 1].splitlines())
        if at is not None:
            caption_lines.setdefault(f, {})[cpage] = [at]
    hits: List[FloatHit] = []
    for f, fpage in captions.items():
        foreign: Dict[int, List[int]] = {}
        for g, per_page in caption_lines.items():
            if g is not f:
                for pg, idxs in per_page.items():
                    foreign.setdefault(pg, []).extend(idxs)
        rpage = _first_ref_page(f, pages, fpage, foreign)
        if rpage is None:
            unmatched.append(f.name)
            continue
        fsec = f.section or _section_at(fpage, pdf_sections)
        rsec = _section_at(rpage, pdf_sections)
        if _is_appendix(fsec):
            continue
        reasons = []
        if abs(fpage - rpage) > max_gap:
            reasons.append(f"{abs(fpage - rpage)} pages from its first reference")
        if fpage != rpage and fsec != rsec and fsec and rsec:
            reasons.append(f"renders in section {fsec} but is first referenced in section {rsec}")
        if reasons:
            hits.append(FloatHit(f.name, fpage, rpage, fsec, rsec, tuple(reasons)))
    return hits, unmatched


@dataclass
class FloatProximityResult:
    version_dir: str
    hits: List[FloatHit] = field(default_factory=list)
    unmatched: List[str] = field(default_factory=list)
    skipped_reason: Optional[str] = None

    def passed(self) -> bool:
        return not self.hits

    def to_json(self) -> dict:
        return {
            "version_dir": self.version_dir,
            "pass": self.passed(),
            "skipped_reason": self.skipped_reason,
            "hits": [h.to_dict() for h in self.hits],
            "unmatched": list(self.unmatched),
        }

    def to_review(self, *, version_dir: str, critic_id: str = CRITIC_ID) -> Review:
        if self.skipped_reason:
            justification = (
                f"float-proximity pre-flight skipped (fail-open): {self.skipped_reason}."
            )
        else:
            justification = (
                "float-proximity pre-flight is a deterministic advisory scan "
                "of the compiled PDF/.aux; owns no rubric dim."
            )
        findings = [
            Finding(
                severity="minor",
                dimension=DIM_FLOAT,
                evidence_span=f"{self.version_dir}: {h.name} (page {h.float_page})",
                rationale=(
                    f"{h.name} renders on page {h.float_page}; its first reference "
                    f"is on page {h.ref_page}: " + "; ".join(h.reasons) + "."
                ),
                suggested_fix=(
                    f"Move {h.name} next to its first reference (adjust placement or "
                    f"float position), or move the first reference next to the float."
                ),
                tool_calls=[],
            )
            for h in self.hits
        ]
        return Review(
            schema_version="1",
            kind=Kind.TOOL_EVIDENCE,
            version_dir=version_dir,
            critic_id=critic_id,
            scores=[Score(dimension=CHECK_NAME, score=None, max=1, justification=justification)],
            findings=findings,
            critical_flags=[],
        )


def _find_sibling(version_dir: Path, stem: str, ext: str) -> Optional[Path]:
    for cand in (version_dir / f"{stem}{ext}", version_dir / "build" / f"{stem}{ext}"):
        if cand.is_file():
            return cand
    return None


def check_float_proximity(
    version_dir: Path,
    *,
    body: Optional[Path] = None,
    max_gap: int = MAX_PAGE_GAP,
) -> FloatProximityResult:
    """Run the pre-flight against a version directory; fails open."""
    version_dir = Path(version_dir).resolve()
    if not version_dir.is_dir():
        raise FileNotFoundError(f"float_proximity: version_dir {version_dir!s} is not a directory.")
    result = FloatProximityResult(version_dir=version_dir.name)
    try:
        stem = resolve_body_path(version_dir, body=body, caller_name=CHECK_NAME).stem
    except FileNotFoundError:
        stem = "main"
    aux = _find_sibling(version_dir, stem, ".aux")
    if aux is None:
        result.skipped_reason = REASON_NO_AUX
        return result
    pdf = _find_sibling(version_dir, stem, ".pdf")
    if pdf is None:
        result.skipped_reason = REASON_NO_PDF
        return result
    text = _extract_pdf_text(pdf)
    if text is None:
        result.skipped_reason = REASON_NO_TEXT
        return result
    aux_text = aux.read_text(encoding="utf-8", errors="replace")
    if not parse_aux(aux_text)[0]:
        result.skipped_reason = REASON_NO_FLOATS
        return result
    pages = text.split("\f")
    if pages and not pages[-1].strip():
        pages.pop()
    result.hits, result.unmatched = analyze(aux_text, pages, max_gap=max_gap)
    return result


def write_review_dir(
    version_dir: Path,
    result: FloatProximityResult,
    *,
    critic_id: str = CRITIC_ID,
) -> Path:
    """Write ``<version_dir>.floats/_review.json`` (atomic, regenerating)."""
    version_dir = Path(version_dir)
    review = result.to_review(version_dir=version_dir.name, critic_id=critic_id)
    return write_critic_review_dir(version_dir, FLOATS_SUFFIX, review)


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.float_proximity",
        description=(
            "Deterministic float-proximity pre-flight (advisory): flags figures "
            "and tables rendered more than one page, or in a different section, "
            "from their first reference. Fails open without a compiled PDF/.aux. "
            "Exit 1 signals findings; it is NOT a blocking verdict."
        ),
    )
    p.add_argument("version_dir", help="Path to <thread>.{N}/.")
    p.add_argument("--write-review", action="store_true",
                   help="Also write <version_dir>.floats/_review.json (staged_sidecar).")
    p.add_argument("--body", metavar="PATH", default=None,
                   help="Override body-file discovery (adopted-in-place legacy threads).")
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. ``0`` clean/skipped, ``1`` findings (advisory), ``2`` error."""
    args = _build_cli_parser().parse_args(argv)
    try:
        result = check_float_proximity(
            Path(args.version_dir), body=Path(args.body) if args.body else None
        )
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result.to_json(), indent=2))
    if result.skipped_reason:
        print(f"float_proximity: skipped ({result.skipped_reason})", file=sys.stderr)
    if args.write_review:
        out = write_review_dir(Path(args.version_dir), result)
        print(f"wrote {out}", file=sys.stderr)
    return 0 if result.passed() else 1


__all__ = [
    "CRITIC_ID",
    "CHECK_NAME",
    "FLOATS_SUFFIX",
    "FloatEntry",
    "FloatHit",
    "FloatProximityResult",
    "parse_aux",
    "analyze",
    "check_float_proximity",
    "write_review_dir",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
