"""poppler-utils probes for the issue-#692 render checks (issue #1128 split).

``pdftotext`` / ``pdfimages`` resolution + invocation for the glyph-
verification and embedded-image-assertion checks (issue #692): the
source-driven non-ASCII codepoint sweep, the source-vs-PDF glyph-drop
comparison, and the body image-reference counter. Split out of the
former monolithic ``anvil/lib/render_gate.py`` along its existing
section banners — see ``anvil/lib/render_gate/__init__.py`` for the
full package rationale.
"""

from __future__ import annotations

import shutil
import subprocess
import unicodedata
from pathlib import Path
from typing import Iterable, Optional

from anvil.lib.render_gate.constants import (
    _MD_IMAGE_REF_RE,
    _strip_nonrendered_regions,
)


#
# ``pdftotext`` and ``pdfimages`` ship in the SAME poppler-utils package as the
# already-consumed ``pdfinfo`` / ``pdftoppm`` (no new binary family for the
# whole issue). Each has a ``_which_*`` resolver mirroring ``_which_pdfinfo``
# and degrades gracefully (records a ``reasons`` breadcrumb, never raises,
# never fails the gate) when the binary is absent — the same contract every
# other external-tool check in this module honors.


def _which_pdftotext(override: Optional[str]) -> Optional[str]:
    """Resolve the ``pdftotext`` executable path, honoring the override."""
    if override is not None:
        return override
    return shutil.which("pdftotext")


def _which_pdfimages(override: Optional[str]) -> Optional[str]:
    """Resolve the ``pdfimages`` executable path, honoring the override."""
    if override is not None:
        return override
    return shutil.which("pdfimages")


def _extract_pdf_text(
    pdf_path: Path, *, pdftotext_path: Optional[str] = None
) -> Optional[str]:
    """Return the extracted text of ``pdf_path`` via ``pdftotext``, or ``None``.

    Surfaces ``None`` (not raise) when ``pdftotext`` is unavailable, the PDF
    is missing, or the subprocess fails — the graceful-degrade contract shared
    with :func:`_count_pages_with_pdfinfo`. Extracts to stdout (``pdftotext
    <pdf> -``) so no temp file is needed.
    """
    exe = _which_pdftotext(pdftotext_path)
    if exe is None or not pdf_path.exists():
        return None
    try:
        proc = subprocess.run(
            [exe, str(pdf_path), "-"],
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout


def _count_pdf_embedded_images(
    pdf_path: Path, *, pdfimages_path: Optional[str] = None
) -> Optional[int]:
    """Return the count of embedded images via ``pdfimages -list``, or ``None``.

    ``pdfimages -list`` prints a two-line header (column names + a dashed
    rule) followed by one row per embedded image. The image count is the
    number of data rows. Returns ``None`` when ``pdfimages`` is unavailable,
    the PDF is missing, or the subprocess fails (graceful degrade — never
    raises).
    """
    exe = _which_pdfimages(pdfimages_path)
    if exe is None or not pdf_path.exists():
        return None
    try:
        proc = subprocess.run(
            [exe, "-list", str(pdf_path)],
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if proc.returncode != 0:
        return None
    lines = [ln for ln in proc.stdout.splitlines() if ln.strip()]
    # Header shape (poppler): a column-name line ("page   num  type ...")
    # then a dashed separator ("--------------------"), then N data rows. A
    # PDF with zero embedded images prints only the two header lines (or, in
    # some poppler builds, nothing at all).
    data_rows = 0
    for ln in lines:
        stripped = ln.strip()
        # Skip the dashed separator rule.
        if set(stripped) <= {"-"}:
            continue
        # Skip the column-name header (starts with "page").
        first = stripped.split(None, 1)[0]
        if first.lower() == "page":
            continue
        # A data row's first field is the (integer) page number.
        if first.isdigit():
            data_rows += 1
    return data_rows


def _sweep_nonascii_codepoints(text: str) -> "dict[str, int]":
    """Return a count of every non-ASCII *non-whitespace* codepoint in ``text``.

    Keyed by the character itself (``ord(ch) > 127``). This is the
    source-driven sweep the issue-#692 glyph check is built on: it enumerates
    the *actual* non-ASCII characters the body uses rather than testing a
    hardcoded allow-list, so unknown-unknowns (the STIX ``≠`` drop) are caught
    by construction.

    Unicode-space codepoints (the ``Zs`` category — U+00A0 NBSP, U+2009 thin
    space, U+202F narrow NBSP, …) are excluded: ``pdftotext`` normalizes them
    to an ASCII space in its extraction, so a stray NBSP in the source would
    otherwise short-count against the PDF and false-block the gate at error
    severity. Whitespace normalization is not the glyph-drop failure mode this
    sweep guards against (issue #692).
    """
    counts: dict[str, int] = {}
    for ch in text:
        if ord(ch) <= 127:
            continue
        # Skip Unicode separator-spaces: pdftotext collapses them to ASCII
        # space, so they can never be a real glyph drop.
        if unicodedata.category(ch) == "Zs":
            continue
        counts[ch] = counts.get(ch, 0) + 1
    return counts


def _verify_source_glyphs(
    source_paths: Iterable[Path],
    pdf_text: str,
) -> list[dict]:
    """Return the list of source non-ASCII codepoints dropped from the PDF.

    For every non-ASCII codepoint in the concatenated source bodies, compare
    its source count against its count in ``pdf_text`` (the ``pdftotext``
    extraction). A codepoint whose PDF count is strictly LESS than its source
    count is a glyph-drop finding.

    The comparison is ``>=`` (not ``==``): pandoc/LaTeX text reflow, ligature
    substitution, and whitespace collapse can legitimately inflate the
    PDF-side count of some codepoints, but must NEVER make a glyph disappear.
    A strict ``==`` would false-positive on that legitimate noise; a short
    count is the only real failure mode.

    Three classes of source non-ASCII are excluded before counting so the
    gate does not false-block a valid document: Unicode separator spaces
    (``Zs`` — pdftotext normalizes them to ASCII space, issue #692),
    non-rendered source regions (link/image URL targets, HTML comments,
    autolinks — their glyphs never reach the rendered body, issue #692), and,
    for ``.tex`` sources, unescaped ``%`` LaTeX comments (issue #856 — e.g. a
    comment-only box-drawing section rule). See ``_sweep_nonascii_codepoints``
    and ``_strip_nonrendered_regions``.

    Each finding: ``{codepoint, name, source_count, pdf_count}`` where
    ``codepoint`` is the ``U+XXXX`` hex form and ``name`` the character
    itself. Only codepoints present in the source participate — extra
    non-ASCII in the PDF (e.g. hyphenation or a template glyph) is ignored.
    """
    source_counts: dict[str, int] = {}
    for path in source_paths:
        if not path.exists() or not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        # Exclude non-rendered source regions (link/image URL targets, HTML
        # comments, autolinks, and — for .tex sources — % LaTeX comments)
        # before the sweep: their non-ASCII never reaches the rendered body,
        # so counting it would false-flag a glyph drop.
        text = _strip_nonrendered_regions(text, latex=path.suffix == ".tex")
        for ch, n in _sweep_nonascii_codepoints(text).items():
            source_counts[ch] = source_counts.get(ch, 0) + n

    if not source_counts:
        return []

    pdf_counts = _sweep_nonascii_codepoints(pdf_text)
    dropped: list[dict] = []
    for ch in sorted(source_counts, key=ord):
        src_n = source_counts[ch]
        pdf_n = pdf_counts.get(ch, 0)
        if pdf_n < src_n:
            dropped.append(
                {
                    "codepoint": f"U+{ord(ch):04X}",
                    "name": ch,
                    "source_count": src_n,
                    "pdf_count": pdf_n,
                }
            )
    return dropped


def _count_body_image_refs(source_paths: Iterable[Path]) -> int:
    """Return the number of ``![alt](path)`` inline-image refs across sources.

    Reference-style images and HTML ``<img>`` tags are not counted — the
    primer/report bodies use the inline ``![…](exhibits/…png)`` convention
    exclusively (the drafter-placed reference contract from #690/#695).
    """
    total = 0
    for path in source_paths:
        if not path.exists() or not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        total += len(_MD_IMAGE_REF_RE.findall(text))
    return total

