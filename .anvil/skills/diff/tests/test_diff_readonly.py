"""Read-only-over-inputs regression tests for `anvil:diff` (issue #925).

`anvil:diff` must NEVER write into a version dir, an origin file, or any
other input path -- version dirs are immutable, and that invariant is
load-bearing for the whole framework (the issue's own Constraints
section). These tests hash every input path before and after a full
CLI run (in each of the three modes) and assert byte-for-byte equality,
mirroring the SHA-256 zero-mutation discipline
`anvil:deslop`/`anvil:project-photos`/`anvil:project-scout` use for
their own read-only contracts.

Test filename is distinct per the #58 packaging convention.
"""

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
_CLI_PY = _HERE.parent / "lib" / "cli.py"


def _load_cli():
    name = "diff_cli"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, _CLI_PY)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


cli = _load_cli()


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_files_mode_never_mutates_either_input(tmp_path: Path) -> None:
    left = tmp_path / "before.md"
    right = tmp_path / "after.md"
    left.write_text("Some prose here.\n", encoding="utf-8")
    right.write_text("Some revised prose here.\n", encoding="utf-8")
    before_left, before_right = _sha256(left), _sha256(right)
    before_listing = sorted(p.name for p in tmp_path.iterdir())

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = cli.main(["files", str(left), str(right), "--no-serve"])

    assert rc == 0
    assert _sha256(left) == before_left
    assert _sha256(right) == before_right
    assert sorted(p.name for p in tmp_path.iterdir()) == before_listing


def test_versions_mode_never_mutates_version_dirs_or_sidecar(
    tmp_path: Path,
) -> None:
    thread_dir = tmp_path
    v1 = thread_dir / "acme.1"
    v1.mkdir()
    (v1 / "acme.md").write_text("First version.\n", encoding="utf-8")
    v2 = thread_dir / "acme.2"
    v2.mkdir()
    (v2 / "acme.md").write_text("Second version, revised.\n", encoding="utf-8")
    review_dir = thread_dir / "acme.2.review"
    review_dir.mkdir()
    review_path = review_dir / "_review.json"
    review_path.write_text(
        json.dumps(
            {
                "schema_version": "1",
                "kind": "judgment",
                "version_dir": "acme.2",
                "critic_id": "diff-test",
                "scores": [
                    {"dimension": "1_evidence", "score": 6, "max": 7}
                ],
                "findings": [],
            }
        ),
        encoding="utf-8",
    )

    tracked = {
        v1 / "acme.md": _sha256(v1 / "acme.md"),
        v2 / "acme.md": _sha256(v2 / "acme.md"),
        review_path: _sha256(review_path),
    }
    before_tree = sorted(str(p) for p in thread_dir.rglob("*"))

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = cli.main(["versions", str(thread_dir), "acme", "--no-serve"])

    assert rc == 0
    for path, digest in tracked.items():
        assert _sha256(path) == digest
    assert sorted(str(p) for p in thread_dir.rglob("*")) == before_tree


def test_deslop_mode_never_mutates_origin_or_emit_dir(tmp_path: Path) -> None:
    origin = tmp_path / "site-copy.md"
    origin.write_text("Original sloppy copy.\n", encoding="utf-8")

    thread_dir = tmp_path / "scratch"
    emit_dir = thread_dir / "emit"
    emit_dir.mkdir(parents=True)
    cleaned = emit_dir / "cleaned.txt"
    cleaned.write_text("Cleaned copy.\n", encoding="utf-8")
    rationale = emit_dir / "rationale.md"
    rationale.write_text("# Deslop rationale\n\n- Tightened.\n", encoding="utf-8")

    tracked = {
        origin: _sha256(origin),
        cleaned: _sha256(cleaned),
        rationale: _sha256(rationale),
    }

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = cli.main(
            ["deslop", str(thread_dir), "--origin", str(origin), "--no-serve"]
        )

    assert rc == 0
    for path, digest in tracked.items():
        assert _sha256(path) == digest


def test_out_flag_only_ever_writes_the_named_output_path(tmp_path: Path) -> None:
    """`--out` is the one documented write path -- confirm it writes
    exactly the one file named, nothing else, and inputs stay untouched."""

    left = tmp_path / "before.md"
    right = tmp_path / "after.md"
    left.write_text("a\n", encoding="utf-8")
    right.write_text("b\n", encoding="utf-8")
    before_left, before_right = _sha256(left), _sha256(right)
    out_path = tmp_path / "view.html"

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = cli.main(
            ["files", str(left), str(right), "--no-serve", "--out", str(out_path)]
        )

    assert rc == 0
    assert _sha256(left) == before_left
    assert _sha256(right) == before_right
    assert sorted(p.name for p in tmp_path.iterdir()) == sorted(
        ["before.md", "after.md", "view.html"]
    )
