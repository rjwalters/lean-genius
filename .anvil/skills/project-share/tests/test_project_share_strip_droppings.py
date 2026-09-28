"""Regression test for `anvil:project-share` issue #756.

The `research/` pool is a shared, human-owned directory that anvil never
writes into — it can (and, per the canary studio report, did) accumulate
Python bytecode caches (`__pycache__/*.pyc`, produced by simply importing
a `.py` model once) and macOS `.DS_Store` droppings. The default strip
list did not cover either, so the exporter copied them straight into
`SHARE/research/`, a package headed to an outside recipient — and the
verify step's leak check passed the export as clean because it re-checks
the SAME (too-narrow) strip list.

This test builds a fixture project whose `research/` pool contains a
`__pycache__/` dir (with a `.pyc` inside), a stray `.pyc` outside any
`__pycache__/` dir, and a `.DS_Store` file, runs the full project-share
collect -> plan -> apply -> verify pipeline, and asserts:

- none of `__pycache__`, `*.pyc`, `.DS_Store` land anywhere in the
  exported `SHARE/` tree, and
- `verify_export` reports success (the leak check must not merely be
  silent — it must actually pass because there is nothing to catch).
"""

from __future__ import annotations

import sys
import unittest
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import orchestrate  # noqa: E402
from _share_fixtures import build_full_project  # noqa: E402

NOW = datetime(2026, 7, 28, 12, 0, 0, tzinfo=timezone.utc)


def _add_bytecode_and_os_droppings(project: Path) -> None:
    """Mirror the canary repro: a runnable model in `research/` that has
    been imported at some point, plus a stray OS dropping."""
    research = project / "research"
    pycache = research / "__pycache__"
    pycache.mkdir(parents=True, exist_ok=True)
    (pycache / "18-breakeven-model.cpython-314.pyc").write_bytes(
        b"\x00fake bytecode\x00"
    )
    # A stray .pyc that landed outside any __pycache__/ dir.
    (research / "sources" / "stray.pyc").parent.mkdir(
        parents=True, exist_ok=True
    )
    (research / "sources" / "stray.pyc").write_bytes(b"\x00stray bytecode\x00")
    # macOS Finder dropping.
    (research / ".DS_Store").write_bytes(b"\x00\x00fake ds_store\x00\x00")


class TestBytecodeAndOsDroppingsStripped(unittest.TestCase):
    def test_export_tree_has_no_bytecode_or_ds_store(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            _add_bytecode_and_os_droppings(project)

            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)

            share = project / "SHARE"
            all_paths = list(share.rglob("*"))

            # No __pycache__ directory anywhere in the export.
            self.assertFalse(
                any(p.name == "__pycache__" for p in all_paths),
                f"__pycache__ leaked into export: {all_paths}",
            )
            # No .pyc file anywhere (inside or outside __pycache__).
            self.assertFalse(
                any(p.suffix == ".pyc" for p in all_paths),
                f".pyc leaked into export: {all_paths}",
            )
            # No .DS_Store anywhere.
            self.assertFalse(
                any(p.name == ".DS_Store" for p in all_paths),
                f".DS_Store leaked into export: {all_paths}",
            )
            # The legitimate research content still exported.
            self.assertTrue(
                (share / "research" / "industry-notes.md").is_file()
            )
            self.assertTrue(
                (
                    share
                    / "research"
                    / "sources"
                    / "robotics-survey.pdf"
                ).is_file()
            )

    def test_verify_passes_clean(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            _add_bytecode_and_os_droppings(project)

            result = orchestrate.run(project, now=NOW)
            assert result.verify_result is not None
            self.assertTrue(
                result.verify_result.ok, result.verify_result.failures
            )
            self.assertGreater(result.verify_result.checks_run, 0)


if __name__ == "__main__":
    unittest.main()
