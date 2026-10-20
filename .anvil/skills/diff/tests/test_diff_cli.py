"""Tests for `anvil/skills/diff/lib/cli.py` (issue #925).

Mirrors the ``project-share``/``cli.py`` precedent (issue #755): a
directly runnable argparse entry point that loads its sibling `lib/`
package via ``anvil.lib.skill_lib_loader`` at call time (not at module
import time -- module-level imports stay stdlib-only, verified in a
subprocess with a stripped ``sys.path``).

Covered:

- CLI module present + module-level imports are stdlib-only.
- ``files`` mode happy path with ``--no-serve``: exit 0, HTML printed,
  nothing written (no ``--out``).
- ``files`` mode with ``--out``: the HTML lands at the given path.
- ``versions`` mode happy path against two real version dirs (with a
  ``.review`` sidecar on the newer one) — exit 0, overlay content present.
- ``deslop`` mode happy path against a real ``emit/`` dir.
- Missing-file / missing-version error paths: exit 1, diagnostic on
  stderr, nothing written.

Test filename is distinct per the #58 packaging convention.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
_LIB_DIR = _HERE.parent / "lib"
_CLI_PY = _LIB_DIR / "cli.py"


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


class TestCliModuleShape(unittest.TestCase):
    def test_cli_file_present(self) -> None:
        self.assertTrue(_CLI_PY.is_file(), f"missing CLI module: {_CLI_PY}")

    def test_module_import_is_stdlib_only(self) -> None:
        with TemporaryDirectory() as td:
            code = (
                "import sys; "
                "sys.path = [p for p in sys.path if p not in ('', '.')]; "
                "import importlib.util as u; "
                f"s = u.spec_from_file_location('cli_probe', {str(_CLI_PY)!r}); "
                "m = u.module_from_spec(s); s.loader.exec_module(m); "
                "print('ok')"
            )
            env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
            result = subprocess.run(
                [sys.executable, "-c", code],
                capture_output=True,
                text=True,
                cwd=td,
                env=env,
            )
        self.assertEqual(
            result.returncode, 0, f"standalone import failed:\n{result.stderr}"
        )
        self.assertIn("ok", result.stdout)


class TestCliFilesMode(unittest.TestCase):
    def test_no_serve_prints_html_and_writes_nothing(self) -> None:
        with TemporaryDirectory() as td:
            left = Path(td) / "before.md"
            right = Path(td) / "after.md"
            left.write_text("The cat sat.\n", encoding="utf-8")
            right.write_text("The cat sat quietly.\n", encoding="utf-8")

            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = cli.main(
                    ["files", str(left), str(right), "--no-serve", "--lint", "none"]
                )
            self.assertEqual(rc, 0)
            out = buf.getvalue()
            self.assertIn("<!DOCTYPE html>", out)
            self.assertIn("quietly", out)
            # No stray output files.
            self.assertEqual(sorted(p.name for p in Path(td).iterdir()), ["after.md", "before.md"])

    def test_out_flag_writes_html_file(self) -> None:
        with TemporaryDirectory() as td:
            left = Path(td) / "before.md"
            right = Path(td) / "after.md"
            left.write_text("a\n", encoding="utf-8")
            right.write_text("b\n", encoding="utf-8")
            out_path = Path(td) / "view.html"

            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = cli.main(
                    [
                        "files",
                        str(left),
                        str(right),
                        "--no-serve",
                        "--out",
                        str(out_path),
                        "--lint",
                        "none",
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertTrue(out_path.is_file())
            self.assertIn("<!DOCTYPE html>", out_path.read_text(encoding="utf-8"))

    def test_missing_file_exits_nonzero(self) -> None:
        with TemporaryDirectory() as td:
            left = Path(td) / "before.md"
            left.write_text("a\n", encoding="utf-8")
            buf_out, buf_err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(buf_out), contextlib.redirect_stderr(
                buf_err
            ):
                rc = cli.main(
                    ["files", str(left), str(Path(td) / "missing.md"), "--no-serve"]
                )
            self.assertEqual(rc, 1)
            self.assertIn("not found", buf_err.getvalue())


class TestCliVersionsMode(unittest.TestCase):
    def test_versions_mode_with_review_overlay(self) -> None:
        with TemporaryDirectory() as td:
            thread_dir = Path(td)
            v1 = thread_dir / "acme.1"
            v1.mkdir()
            (v1 / "acme.md").write_text("Opening line.\nSecond line.\n", encoding="utf-8")

            v2 = thread_dir / "acme.2"
            v2.mkdir()
            (v2 / "acme.md").write_text(
                "Opening line revised.\nSecond line.\n", encoding="utf-8"
            )
            review_dir = thread_dir / "acme.2.review"
            review_dir.mkdir()
            (review_dir / "_review.json").write_text(
                json.dumps(
                    {
                        "schema_version": "1",
                        "kind": "judgment",
                        "version_dir": "acme.2",
                        "critic_id": "diff-test",
                        "scores": [
                            {
                                "dimension": "9_rhetorical_economy",
                                "score": 6,
                                "max": 7,
                                "evidence_span": "acme.md:L1",
                                "justification": "Tightened.",
                            }
                        ],
                        "findings": [],
                    }
                ),
                encoding="utf-8",
            )

            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = cli.main(
                    ["versions", str(thread_dir), "acme", "--no-serve", "--lint", "none"]
                )
            self.assertEqual(rc, 0)
            out = buf.getvalue()
            self.assertIn("Tightened", out)
            self.assertIn("revised", out)

    def test_versions_mode_missing_thread_exits_nonzero(self) -> None:
        with TemporaryDirectory() as td:
            buf_out, buf_err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(buf_out), contextlib.redirect_stderr(
                buf_err
            ):
                rc = cli.main(["versions", td, "acme", "--no-serve"])
            self.assertEqual(rc, 1)
            self.assertTrue(buf_err.getvalue())


class TestCliDeslopMode(unittest.TestCase):
    def test_deslop_mode_happy_path(self) -> None:
        with TemporaryDirectory() as td:
            origin = Path(td) / "site-copy.md"
            origin.write_text("We delve into the details.\n", encoding="utf-8")

            thread_dir = Path(td) / "scratch"
            emit_dir = thread_dir / "emit"
            emit_dir.mkdir(parents=True)
            (emit_dir / "cleaned.txt").write_text(
                "We explain the details.\n", encoding="utf-8"
            )
            (emit_dir / "rationale.md").write_text(
                "# Deslop rationale\n\n- Replaced 'delve' with a plain verb.\n",
                encoding="utf-8",
            )

            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = cli.main(
                    [
                        "deslop",
                        str(thread_dir),
                        "--origin",
                        str(origin),
                        "--no-serve",
                        "--lint",
                        "none",
                    ]
                )
            self.assertEqual(rc, 0)
            out = buf.getvalue()
            self.assertIn("explain", out)
            self.assertIn("Replaced", out)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
