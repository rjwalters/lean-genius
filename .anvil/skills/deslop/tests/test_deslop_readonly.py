"""Read-only-over-the-source regression tests for `anvil:deslop` (issue #898).

`anvil:deslop` must NEVER write to an ingested source file — the operator
applies the emitted diff themselves. These tests hash the source before
and after a full ingest -> lint -> review -> emit pass and assert
byte-for-byte equality, mirroring the SHA-256 zero-mutation discipline
`anvil:project-photos`/`anvil:project-scout` use for their own read-only
contracts.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

from _deslop_fixtures import CLEAN_MARKDOWN, SLOPPY_HTML, SLOPPY_MARKDOWN
from _deslop_skill_lib import ingest, orchestrate


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run_full_pass(src: Path, tmp_path: Path, final_prose: str) -> None:
    item = ingest.ingest_path(src)
    orchestrate.lint_body(item.prose, project_dir=None)

    thread_dir = orchestrate.init_thread(tmp_path / "scratch", orchestrate.slugify(item.label))
    orchestrate.write_version(thread_dir, 1, item.prose)
    review = orchestrate.new_review(
        version_dir_name=orchestrate.version_dir_name(thread_dir, 1),
        rhetorical_economy=5,
        voice_adherence=None,
    )
    orchestrate.write_critic_review(thread_dir, 1, review)
    orchestrate.aggregate_reviews(thread_dir, 1)
    orchestrate.emit(thread_dir, item, final_prose, ["Tightened the opener."])


def test_full_pass_never_mutates_markdown_source(tmp_path: Path) -> None:
    src = tmp_path / "copy.md"
    src.write_text(SLOPPY_MARKDOWN, encoding="utf-8")
    before = _sha256(src)

    _run_full_pass(src, tmp_path, CLEAN_MARKDOWN)

    after = _sha256(src)
    assert before == after
    assert src.read_text(encoding="utf-8") == SLOPPY_MARKDOWN


def test_full_pass_never_mutates_html_source(tmp_path: Path) -> None:
    src = tmp_path / "index.html"
    src.write_text(SLOPPY_HTML, encoding="utf-8")
    before = _sha256(src)

    _run_full_pass(src, tmp_path, "Our Product\n\nShips faster.\n")

    after = _sha256(src)
    assert before == after


def test_ingest_alone_never_writes_anything(tmp_path: Path) -> None:
    src = tmp_path / "copy.md"
    src.write_text(SLOPPY_MARKDOWN, encoding="utf-8")
    before_listing = sorted(p.name for p in tmp_path.iterdir())

    ingest.ingest_path(src)

    after_listing = sorted(p.name for p in tmp_path.iterdir())
    assert before_listing == after_listing
