"""Prose ingestion for `anvil:deslop` (issue #898).

Extracts the prose to iterate on from either a **file path** (markdown or
HTML) or **pasted plain text**, keeping a map back to the origin so the
operator can apply the eventual diff themselves. This module never writes
to an ingested file — it only reads.

v1 scope note (issue #898 curator scope note): JSX/TSX/JS/TS
source-literal string extraction is explicitly OUT of scope. A repo-wide
search against the tree at curation time found zero existing precedent
for JSX/HTML-in-source parsing anywhere in ``anvil/lib/`` or any skill —
that is net-new parsing infrastructure, tracked as a separate follow-up.
:func:`ingest_path` raises :class:`UnsupportedInputError` naming the
file when asked to ingest one of those suffixes, rather than silently
mis-extracting.
"""

from __future__ import annotations

from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path
from typing import List, Optional, Union


# File suffixes this v1 ingester knows how to extract prose from.
MARKDOWN_SUFFIXES = {".md", ".markdown", ".mdx"}
HTML_SUFFIXES = {".html", ".htm"}

# Explicitly out of scope for v1 (issue #898 curator scope note): source
# files whose prose lives in string literals require a JSX/TS-aware
# parser this issue does not build. Named here so the ingester fails
# loud with a scope-accurate message instead of mis-extracting raw
# source as prose.
UNSUPPORTED_SUFFIXES = {".jsx", ".tsx", ".js", ".ts", ".vue", ".svelte"}


class UnsupportedInputError(ValueError):
    """Raised when asked to ingest a file this v1 ingester cannot handle."""


# ---------------------------------------------------------------------------
# HTML visible-text extraction
# ---------------------------------------------------------------------------


class _VisibleTextExtractor(HTMLParser):
    """Minimal stdlib HTML -> visible-text extractor.

    Drops ``<script>``/``<style>``/``<head>``/``<title>`` content entirely
    and inserts a paragraph break at block-level tag boundaries so the
    extracted prose keeps enough structure for line-based lint/diff to be
    meaningful. Deliberately conservative: this is NOT a full HTML->text
    renderer (no table layout, no list-marker synthesis) — it is a
    "get the reader-visible words out, plainly" extractor, sized to the
    website-copy / README-fragment use case in the issue.
    """

    _BLOCK_TAGS = {
        "p", "div", "section", "article", "header", "footer", "li",
        "h1", "h2", "h3", "h4", "h5", "h6", "br", "ul", "ol", "blockquote",
        "tr", "table", "main", "nav", "aside", "figcaption",
    }
    _SKIP_TAGS = {"script", "style", "head", "title", "noscript", "template"}

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self._chunks: List[str] = []
        self._skip_depth = 0

    def handle_starttag(self, tag: str, attrs) -> None:  # noqa: ANN001
        if tag in self._SKIP_TAGS:
            self._skip_depth += 1
        elif tag in self._BLOCK_TAGS:
            self._chunks.append("\n")

    def handle_startendtag(self, tag: str, attrs) -> None:  # noqa: ANN001
        # Self-closing tags (e.g. <br/>) never open a skip region.
        if tag in self._BLOCK_TAGS:
            self._chunks.append("\n")

    def handle_endtag(self, tag: str) -> None:
        if tag in self._SKIP_TAGS:
            if self._skip_depth > 0:
                self._skip_depth -= 1
        elif tag in self._BLOCK_TAGS:
            self._chunks.append("\n")

    def handle_data(self, data: str) -> None:
        if self._skip_depth:
            return
        self._chunks.append(data)

    def get_text(self) -> str:
        raw = "".join(self._chunks)
        # Collapse intra-line whitespace but preserve the paragraph breaks
        # the block-tag boundaries inserted above.
        lines = [" ".join(ln.split()) for ln in raw.splitlines()]
        out_lines: List[str] = []
        blank_run = True  # suppress leading blank lines
        for ln in lines:
            if ln:
                out_lines.append(ln)
                blank_run = False
            elif not blank_run:
                out_lines.append("")
                blank_run = True
        while out_lines and out_lines[-1] == "":
            out_lines.pop()
        text = "\n".join(out_lines)
        return text + "\n" if text else ""


def extract_html_text(html: str) -> str:
    """Extract reader-visible prose from an HTML document/fragment.

    Strips ``<script>``/``<style>``/``<head>`` content, collapses
    whitespace, and inserts blank lines at block-tag boundaries. Pure
    function of the input string — no filesystem access.
    """
    parser = _VisibleTextExtractor()
    parser.feed(html)
    parser.close()
    return parser.get_text()


# ---------------------------------------------------------------------------
# Ingested item + entry points
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class IngestedItem:
    """One ingested prose source, with a map back to its origin.

    ``origin`` is ``None`` for pasted text (there is no file to apply a
    diff to — the emitted diff for a pasted-text item is presented as the
    plain revised text, not a unified diff against a source file).
    """

    origin: Optional[str]  # absolute path string, or None for pasted text
    origin_kind: str  # "markdown-file" | "html-file" | "text-file" | "pasted-text"
    original_text: str  # raw original content (file text, or the pasted string)
    prose: str  # extracted plain text used for lint/critique/iteration
    label: str  # short human label for reporting / diff headers


def ingest_path(path: Union[str, Path]) -> IngestedItem:
    """Ingest one file path. Read-only — never writes to ``path``.

    Dispatches by suffix: markdown/plain-text files pass through
    unchanged (the body itself IS the prose being cleaned up —
    ``rhetoric_lint``'s markdown-aware stripping is a documented no-op
    on prose that carries no fences/HTML-comments/inline-code), HTML
    files run through :func:`extract_html_text`. Raises
    :class:`UnsupportedInputError` for a JSX/TSX/JS/TS/Vue/Svelte source
    file (out of scope for v1 — see module docstring).
    """
    p = Path(path)
    if not p.is_file():
        raise FileNotFoundError(f"deslop ingest: not a file: {p}")

    suffix = p.suffix.lower()
    if suffix in UNSUPPORTED_SUFFIXES:
        raise UnsupportedInputError(
            f"deslop ingest: {p} — JSX/TSX/JS/TS source-literal string "
            "extraction is out of scope for anvil:deslop v1 (issue #898 "
            "curator scope note). Extract the target prose into a "
            "markdown, HTML, or plain-text file (or paste it directly) "
            "and re-run."
        )

    raw = p.read_text(encoding="utf-8")

    if suffix in HTML_SUFFIXES:
        return IngestedItem(
            origin=str(p.resolve()),
            origin_kind="html-file",
            original_text=raw,
            prose=extract_html_text(raw),
            label=p.name,
        )

    origin_kind = "markdown-file" if suffix in MARKDOWN_SUFFIXES else "text-file"
    return IngestedItem(
        origin=str(p.resolve()),
        origin_kind=origin_kind,
        original_text=raw,
        prose=raw,
        label=p.name,
    )


def ingest_pasted(text: str, *, label: str = "pasted-text") -> IngestedItem:
    """Ingest a raw pasted-text string. There is no file, hence no origin."""
    return IngestedItem(
        origin=None,
        origin_kind="pasted-text",
        original_text=text,
        prose=text,
        label=label,
    )


def ingest_inputs(inputs: List[str]) -> List[IngestedItem]:
    """Ingest a mix of file paths and pasted-text strings.

    An entry that resolves to an existing file on disk is ingested via
    :func:`ingest_path` (dispatched by suffix); anything else is treated
    as pasted text verbatim via :func:`ingest_pasted`. This mirrors how
    an operator invokes the skill —
    ``/anvil:deslop path/to/copy.md "some pasted paragraph..."`` — without
    requiring a separate flag to distinguish the two.
    """
    items: List[IngestedItem] = []
    for index, entry in enumerate(inputs):
        candidate = Path(entry)
        if candidate.is_file():
            items.append(ingest_path(candidate))
        else:
            items.append(ingest_pasted(entry, label=f"pasted-text-{index + 1}"))
    return items


__all__ = [
    "MARKDOWN_SUFFIXES",
    "HTML_SUFFIXES",
    "UNSUPPORTED_SUFFIXES",
    "UnsupportedInputError",
    "IngestedItem",
    "extract_html_text",
    "ingest_path",
    "ingest_pasted",
    "ingest_inputs",
]
