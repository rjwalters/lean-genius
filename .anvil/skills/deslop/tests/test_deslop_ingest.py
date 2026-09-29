"""Tests for `anvil:deslop`'s ingest module (issue #898).

Covers markdown-file, HTML-file, and pasted-text extraction, mixed-input
dispatch, and the JSX/TSX out-of-scope refusal.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from _deslop_fixtures import CLEAN_MARKDOWN, PASTED_SLOPPY_TEXT, SLOPPY_HTML
from _deslop_skill_lib import ingest


def test_ingest_markdown_file_prose_is_raw_body(tmp_path: Path) -> None:
    md_path = tmp_path / "copy.md"
    md_path.write_text(CLEAN_MARKDOWN, encoding="utf-8")

    item = ingest.ingest_path(md_path)

    assert item.origin == str(md_path.resolve())
    assert item.origin_kind == "markdown-file"
    assert item.original_text == CLEAN_MARKDOWN
    # For markdown, the body IS the prose — no transformation.
    assert item.prose == CLEAN_MARKDOWN
    assert item.label == "copy.md"


def test_ingest_plain_text_file(tmp_path: Path) -> None:
    txt_path = tmp_path / "readme-fragment.txt"
    txt_path.write_text("Ship faster with less ceremony.\n", encoding="utf-8")

    item = ingest.ingest_path(txt_path)

    assert item.origin_kind == "text-file"
    assert item.prose == item.original_text


def test_ingest_html_file_extracts_visible_text_only(tmp_path: Path) -> None:
    html_path = tmp_path / "index.html"
    html_path.write_text(SLOPPY_HTML, encoding="utf-8")

    item = ingest.ingest_path(html_path)

    assert item.origin_kind == "html-file"
    assert item.original_text == SLOPPY_HTML
    # Script/style/title content must never leak into the extracted prose.
    assert "ignore me" not in item.prose.lower()
    assert "color:red" not in item.prose
    # But the reader-visible copy does show up.
    assert "Our Product" in item.prose
    assert "important to note" in item.prose


def test_extract_html_text_collapses_whitespace_and_keeps_paragraph_breaks() -> None:
    html = "<body><p>Hello   world</p><p>Second   paragraph</p></body>"
    text = ingest.extract_html_text(html)
    assert "Hello world" in text
    assert "Second paragraph" in text
    # A blank line separates the two paragraphs.
    assert "\n\n" in text


def test_ingest_pasted_text_has_no_origin() -> None:
    item = ingest.ingest_pasted(PASTED_SLOPPY_TEXT)

    assert item.origin is None
    assert item.origin_kind == "pasted-text"
    assert item.prose == PASTED_SLOPPY_TEXT
    assert item.original_text == PASTED_SLOPPY_TEXT


def test_ingest_inputs_dispatches_files_and_pasted_text(tmp_path: Path) -> None:
    md_path = tmp_path / "a.md"
    md_path.write_text(CLEAN_MARKDOWN, encoding="utf-8")

    items = ingest.ingest_inputs([str(md_path), PASTED_SLOPPY_TEXT])

    assert len(items) == 2
    assert items[0].origin_kind == "markdown-file"
    assert items[1].origin_kind == "pasted-text"
    assert items[1].origin is None


def test_ingest_missing_file_raises(tmp_path: Path) -> None:
    with pytest.raises(FileNotFoundError):
        ingest.ingest_path(tmp_path / "does-not-exist.md")


@pytest.mark.parametrize("suffix", [".jsx", ".tsx", ".js", ".ts", ".vue", ".svelte"])
def test_ingest_jsx_tsx_family_is_out_of_scope(tmp_path: Path, suffix: str) -> None:
    src_path = tmp_path / f"Component{suffix}"
    src_path.write_text("const x = <div>hello</div>;\n", encoding="utf-8")

    with pytest.raises(ingest.UnsupportedInputError, match="out of scope"):
        ingest.ingest_path(src_path)
