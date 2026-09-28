"""Tests for `anvil/skills/project-share/lib/cli.py` (issue #755).

Issue #755: `commands/project-share.md` documented the flow as "one
library call — `orchestrate.run(project_dir, ...)`", but there was no
runnable path to that call in a consumer install. The skill's `lib/`
modules use relative imports (`from .apply import ...`) so they must be
imported as a package, and the skill directory name (`project-share`)
is not a valid Python package identifier, so
`anvil.skills.project_share.lib` never resolves. The studio canary had
to hand-roll a ~30-line importlib driver. The fix ships `lib/cli.py` —
a directly runnable argparse entry point mirroring
`memo/lib/render_phase.py` — that loads the sibling lib package under a
synthetic name and calls `orchestrate.run`.

Covered:

- CLI module present + module-level imports are stdlib-only (the #199
  standalone-import discipline: importable without the framework or the
  skill's own relative-import package on `sys.path`).
- `main()` dry-run happy path: exit 0, report printed, nothing written.
- `main()` apply happy path: exit 0, `SHARE/EXPORT.md` written.
- `main()` `--zip`: the datestamped zip is produced.
- `main()` unresolved-doc path: exit 1 (the rest still exports).
- `main()` bad project dir: exit 1 with a diagnostic on stderr.
- End-to-end subprocess run from the source tree.
- Doc contract: `commands/project-share.md` shows the runnable
  `cli.py` invocation.

Per the #58 packaging convention this filename
(`test_project_share_cli.py`) is unique across the
`anvil/skills/*/tests/` tree. The CLI module itself is loaded under a
unique synthetic name (`project_share_cli`) via importlib so the
generic basename `cli` never collides in `sys.modules` with a future
skill's `cli.py`.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import os
import subprocess
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _share_fixtures import (  # noqa: E402
    build_full_project,
    build_project_with_unstarted_slug,
)

_LIB_DIR = _HERE.parent / "lib"
_CLI_PY = _LIB_DIR / "cli.py"
_COMMAND_DOC = _HERE.parent / "commands" / "project-share.md"


def _load_cli():
    """Load ``cli.py`` under a unique synthetic module name.

    Loading by file path under ``project_share_cli`` (rather than a bare
    ``import cli`` off ``sys.path``) keeps the generic ``cli`` basename
    from colliding in ``sys.modules`` with any other skill that later
    ships its own ``lib/cli.py``.
    """
    name = "project_share_cli"
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
        """Importing ``cli`` must not require the framework or the skill's
        own relative-import ``lib`` package.

        The #199 standalone-import discipline: module-level imports are
        stdlib-only; ``anvil.lib.*`` and the sibling lib modules are
        loaded lazily inside :func:`main`. Verified in a subprocess with
        a stripped ``sys.path`` so neither the repo-root ``anvil/``
        package nor the ``lib/`` dir can leak in.
        """
        with TemporaryDirectory() as td:
            code = (
                "import sys; "
                "sys.path = [p for p in sys.path if p not in ('', '.')]; "
                f"import importlib.util as u; "
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


class TestCliDryRun(unittest.TestCase):
    def test_dry_run_prints_report_and_writes_nothing(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = cli.main([str(project), "--dry-run"])
            self.assertEqual(rc, 0)
            out = buf.getvalue()
            self.assertIn("Project share", out)
            self.assertIn("dry-run", out)
            self.assertFalse((project / "SHARE").exists())

    def test_unresolved_doc_exits_nonzero(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_unstarted_slug(Path(td))
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = cli.main([str(project), "--dry-run"])
            # An unresolved doc is a finding, not a hard error — exit 1.
            self.assertEqual(rc, 1)
            self.assertIn("unstarted-deck", buf.getvalue())


class TestCliApply(unittest.TestCase):
    def test_apply_writes_share_folder(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = cli.main([str(project)])
            self.assertEqual(rc, 0)
            self.assertTrue((project / "SHARE" / "EXPORT.md").is_file())

    def test_zip_flag_produces_archive(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            with contextlib.redirect_stdout(io.StringIO()):
                rc = cli.main([str(project), "--zip"])
            self.assertEqual(rc, 0)
            self.assertTrue(list(project.glob("*-share-*.zip")))


class TestCliErrors(unittest.TestCase):
    def test_missing_project_dir_exits_one_with_stderr(self) -> None:
        with TemporaryDirectory() as td:
            missing = Path(td) / "does-not-exist"
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                rc = cli.main([str(missing)])
            self.assertEqual(rc, 1)
            self.assertIn("project-share cli:", err.getvalue())


class TestCliSubprocess(unittest.TestCase):
    """End-to-end: run the CLI as a real process, as a consumer would."""

    def test_subprocess_dry_run_from_source_tree(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            repo_root = _HERE.parents[3]
            env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
            # The bootstrap walks up from cli.py to the dir containing
            # anvil/__init__.py (the repo root), so no PYTHONPATH is
            # needed even from a hermetic cwd.
            result = subprocess.run(
                [sys.executable, str(_CLI_PY), str(project), "--dry-run"],
                capture_output=True,
                text=True,
                cwd=str(repo_root),
                env=env,
            )
        self.assertEqual(
            result.returncode, 0, f"cli subprocess failed:\n{result.stderr}"
        )
        self.assertIn("Project share", result.stdout)


class TestCliDocContract(unittest.TestCase):
    def test_command_doc_shows_runnable_invocation(self) -> None:
        text = _COMMAND_DOC.read_text(encoding="utf-8")
        self.assertIn("lib/cli.py", text)
        self.assertIn("--dry-run", text)
        self.assertIn("--zip", text)


if __name__ == "__main__":
    unittest.main()
