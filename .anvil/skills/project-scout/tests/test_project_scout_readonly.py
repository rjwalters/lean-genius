"""Zero-mutation contract for `anvil:project-scout` (issue #407, AC 3).

The ENTIRE skill is read-only by construction — not one mode of a
mutating skill. SHA-256 tree check (project-share's dry-run test
pattern, ``test_project_share_dry_run.py::_tree_hash``) across every
code path: default, verbose, include/exclude, and report/json writes
(which the operator directs OUTSIDE the scanned tree). A second run is
byte-identical — the determinism check rides along for free.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from anvil.lib.testing import tree_hash as _tree_hash

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_scout_skill_lib import orchestrate  # noqa: E402
from _scout_fixtures import build_mega_tree  # noqa: E402


class TestZeroMutations(unittest.TestCase):
    def test_default_scan_mutates_nothing(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            build_mega_tree(root)
            before = _tree_hash(root)
            result = orchestrate.run(root)
            self.assertTrue(result.success)
            self.assertEqual(
                before, _tree_hash(root), "scan mutated the tree"
            )

    def test_every_flag_combination_mutates_nothing(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            build_mega_tree(root)
            before = _tree_hash(root)
            for kwargs in (
                {"verbose": True},
                {"include": ("*.md",)},
                {"exclude": ("docs-site", "corp-docs")},
                {
                    "include": ("*.md", "*.tex"),
                    "exclude": ("node_modules",),
                    "verbose": True,
                },
            ):
                with self.subTest(kwargs=kwargs):
                    orchestrate.run(root, **kwargs)
                    self.assertEqual(before, _tree_hash(root))

    def test_report_and_json_writes_stay_outside_tree(self) -> None:
        with TemporaryDirectory() as td_tree, TemporaryDirectory() as td_out:
            root = Path(td_tree).resolve()
            build_mega_tree(root)
            before = _tree_hash(root)
            out = Path(td_out)
            orchestrate.run(
                root,
                verbose=True,
                report_path=out / "scout.md",
                json_path=out / "scout.json",
            )
            self.assertEqual(before, _tree_hash(root))
            self.assertTrue((out / "scout.md").is_file())
            self.assertTrue((out / "scout.json").is_file())

    def test_second_run_byte_identical(self) -> None:
        """Determinism rides along with the SHA check for free."""
        with TemporaryDirectory() as td_tree, TemporaryDirectory() as td_out:
            root = Path(td_tree).resolve()
            build_mega_tree(root)
            out = Path(td_out)
            orchestrate.run(
                root, report_path=out / "a.md", json_path=out / "a.json"
            )
            orchestrate.run(
                root, report_path=out / "b.md", json_path=out / "b.json"
            )
            self.assertEqual(
                (out / "a.md").read_bytes(), (out / "b.md").read_bytes()
            )
            self.assertEqual(
                (out / "a.json").read_bytes(),
                (out / "b.json").read_bytes(),
            )


if __name__ == "__main__":
    unittest.main()
