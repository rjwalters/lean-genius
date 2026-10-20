"""Tests for `anvil:diff`'s input-mode resolution (issue #925).

Covers ``resolve_body_file``, ``enumerate_versions``,
``resolve_version_pair`` (including the pinned-``.latest``-symlink case
via ``anvil.lib.latest_resolution``), and ``resolve_deslop_pair``.

Test filename is distinct per the #58 packaging convention.
"""

from __future__ import annotations

import os
from pathlib import Path

import pytest
from _diff_skill_lib import sources


def _make_version(thread_dir: Path, slug: str, n: int, body: str) -> Path:
    version_dir = thread_dir / f"{slug}.{n}"
    version_dir.mkdir(parents=True, exist_ok=True)
    (version_dir / f"{slug}.md").write_text(body, encoding="utf-8")
    return version_dir


# ---------------------------------------------------------------------------
# resolve_body_file
# ---------------------------------------------------------------------------


def test_resolve_body_file_finds_markdown(tmp_path: Path) -> None:
    version_dir = _make_version(tmp_path, "acme", 1, "hello\n")
    found = sources.resolve_body_file(version_dir)
    assert found == version_dir / "acme.md"


def test_resolve_body_file_finds_tex_when_no_markdown(tmp_path: Path) -> None:
    version_dir = tmp_path / "spec.2"
    version_dir.mkdir()
    (version_dir / "spec.tex").write_text("\\section{X}\n", encoding="utf-8")
    found = sources.resolve_body_file(version_dir)
    assert found == version_dir / "spec.tex"


def test_resolve_body_file_falls_back_to_largest_candidate(tmp_path: Path) -> None:
    version_dir = tmp_path / "thing.1"
    version_dir.mkdir()
    (version_dir / "small.md").write_text("x\n", encoding="utf-8")
    (version_dir / "bigger.md").write_text("x" * 500 + "\n", encoding="utf-8")
    found = sources.resolve_body_file(version_dir, slug="thing")
    assert found == version_dir / "bigger.md"


def test_resolve_body_file_returns_none_when_nothing_found(tmp_path: Path) -> None:
    version_dir = tmp_path / "empty.1"
    version_dir.mkdir()
    assert sources.resolve_body_file(version_dir) is None


def test_resolve_body_file_missing_dir_returns_none(tmp_path: Path) -> None:
    assert sources.resolve_body_file(tmp_path / "nope.1") is None


# ---------------------------------------------------------------------------
# enumerate_versions
# ---------------------------------------------------------------------------


def test_enumerate_versions_sorted(tmp_path: Path) -> None:
    _make_version(tmp_path, "acme", 1, "v1\n")
    _make_version(tmp_path, "acme", 3, "v3\n")
    _make_version(tmp_path, "acme", 2, "v2\n")
    assert sources.enumerate_versions(tmp_path, "acme") == [1, 2, 3]


def test_enumerate_versions_missing_thread_dir(tmp_path: Path) -> None:
    assert sources.enumerate_versions(tmp_path / "nope", "acme") == []


def test_enumerate_versions_ignores_critic_siblings(tmp_path: Path) -> None:
    _make_version(tmp_path, "acme", 1, "v1\n")
    (tmp_path / "acme.1.review").mkdir()
    assert sources.enumerate_versions(tmp_path, "acme") == [1]


# ---------------------------------------------------------------------------
# resolve_version_pair
# ---------------------------------------------------------------------------


def test_resolve_version_pair_defaults_to_latest_and_previous(tmp_path: Path) -> None:
    _make_version(tmp_path, "acme", 1, "v1\n")
    _make_version(tmp_path, "acme", 2, "v2\n")
    _make_version(tmp_path, "acme", 3, "v3\n")

    left, right = sources.resolve_version_pair(tmp_path, "acme")
    assert left.name == "acme.2"
    assert right.name == "acme.3"


def test_resolve_version_pair_explicit_from_to(tmp_path: Path) -> None:
    _make_version(tmp_path, "acme", 1, "v1\n")
    _make_version(tmp_path, "acme", 2, "v2\n")
    _make_version(tmp_path, "acme", 3, "v3\n")

    left, right = sources.resolve_version_pair(tmp_path, "acme", from_n=1, to_n=3)
    assert left.name == "acme.1"
    assert right.name == "acme.3"


def test_resolve_version_pair_honors_pinned_latest_symlink(tmp_path: Path) -> None:
    _make_version(tmp_path, "acme", 1, "v1\n")
    _make_version(tmp_path, "acme", 2, "v2\n")
    _make_version(tmp_path, "acme", 3, "v3\n")
    # Pin .latest at v2 even though v3 exists (issue #288's load-bearing
    # AC, re-verified here through resolve_version_pair's default path).
    os.symlink("acme.2", tmp_path / "acme.latest")

    left, right = sources.resolve_version_pair(tmp_path, "acme")
    assert right == tmp_path / "acme.latest"
    assert left.name == "acme.1"


def test_resolve_version_pair_no_versions_raises(tmp_path: Path) -> None:
    with pytest.raises(sources.VersionPairError):
        sources.resolve_version_pair(tmp_path, "acme")


def test_resolve_version_pair_single_version_requires_explicit_from(
    tmp_path: Path,
) -> None:
    _make_version(tmp_path, "acme", 1, "v1\n")
    with pytest.raises(sources.VersionPairError):
        sources.resolve_version_pair(tmp_path, "acme")


def test_resolve_version_pair_explicit_missing_from_raises(tmp_path: Path) -> None:
    _make_version(tmp_path, "acme", 1, "v1\n")
    with pytest.raises(sources.VersionPairError):
        sources.resolve_version_pair(tmp_path, "acme", from_n=99, to_n=1)


def test_resolve_version_pair_explicit_missing_to_raises(tmp_path: Path) -> None:
    _make_version(tmp_path, "acme", 1, "v1\n")
    with pytest.raises(sources.VersionPairError):
        sources.resolve_version_pair(tmp_path, "acme", to_n=99)


# ---------------------------------------------------------------------------
# resolve_deslop_pair
# ---------------------------------------------------------------------------


def test_resolve_deslop_pair(tmp_path: Path) -> None:
    origin = tmp_path / "index.md"
    origin.write_text("Sloppy prose.\n", encoding="utf-8")

    thread_dir = tmp_path / "scratch" / "index"
    emit_dir = thread_dir / "emit"
    emit_dir.mkdir(parents=True)
    (emit_dir / "cleaned.txt").write_text("Clean prose.\n", encoding="utf-8")
    (emit_dir / "rationale.md").write_text(
        "# Deslop rationale\n\n- Tightened the opener.\n", encoding="utf-8"
    )

    resolved_origin, cleaned, rationale = sources.resolve_deslop_pair(
        thread_dir, origin
    )
    assert resolved_origin == origin
    assert cleaned == emit_dir / "cleaned.txt"
    assert rationale == emit_dir / "rationale.md"


def test_resolve_deslop_pair_missing_cleaned_raises(tmp_path: Path) -> None:
    origin = tmp_path / "index.md"
    origin.write_text("x\n", encoding="utf-8")
    with pytest.raises(sources.VersionPairError):
        sources.resolve_deslop_pair(tmp_path / "scratch", origin)


def test_resolve_deslop_pair_missing_origin_raises(tmp_path: Path) -> None:
    thread_dir = tmp_path / "scratch"
    emit_dir = thread_dir / "emit"
    emit_dir.mkdir(parents=True)
    (emit_dir / "cleaned.txt").write_text("clean\n", encoding="utf-8")
    with pytest.raises(sources.VersionPairError):
        sources.resolve_deslop_pair(thread_dir, tmp_path / "missing.md")


def test_resolve_deslop_pair_no_rationale_is_none(tmp_path: Path) -> None:
    origin = tmp_path / "index.md"
    origin.write_text("x\n", encoding="utf-8")
    thread_dir = tmp_path / "scratch"
    emit_dir = thread_dir / "emit"
    emit_dir.mkdir(parents=True)
    (emit_dir / "cleaned.txt").write_text("y\n", encoding="utf-8")

    _, _, rationale = sources.resolve_deslop_pair(thread_dir, origin)
    assert rationale is None
