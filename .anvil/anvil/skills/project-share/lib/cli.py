#!/usr/bin/env python3
"""Runnable CLI entry point for `anvil:project-share` (issue #755).

`commands/project-share.md` documents the flow as "one library call —
`orchestrate.run(project_dir, ...)`" — but there was no runnable path
to that call in a consumer install:

- `lib/` modules use relative imports (`from .apply import ...`), so
  they must be imported as a package;
- the skill directory name (`project-share`) is not a valid Python
  package name, so `anvil.skills.project_share.lib` never resolves;
- no `__main__.py`, `-m` entry, or CLI script shipped with the skill.

This script is the runnable entry point::

    python3 .anvil/anvil/skills/project-share/lib/cli.py <project-dir> [--dry-run] [--zip]

(from a consumer install; from the anvil source repo the path is
``anvil/skills/project-share/lib/cli.py``).

It loads the sibling ``lib/`` modules the same way
``tests/_project_share_skill_lib.py`` does for the test suite —
``importlib.util.spec_from_file_location`` under a synthetic
``project_share_lib`` package name — so a consumer never has to
hand-roll that ~30-line importlib driver themselves. It then calls
``orchestrate.run(project_dir, dry_run=..., zip_output=...)`` and
prints the markdown report to stdout, exiting nonzero when the run
did not succeed (refused rebuild, verification failure, or an
unresolved doc — see ``orchestrate.RunResult.success``).
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path
from types import ModuleType
from typing import Optional

# Dependency-safe load order: config -> collect -> plan -> citations ->
# apply -> verify -> orchestrate (plan imports collect + config;
# citations + apply + verify import plan; apply also imports
# citations; orchestrate imports everything). Mirrors
# tests/_project_share_skill_lib.py.
_PACKAGE_NAME = "project_share_lib"
_MODULES = [
    "config",
    "collect",
    "plan",
    "citations",
    "apply",
    "verify",
    "orchestrate",
]


def _bootstrap_sys_path() -> None:
    """Make ``import anvil`` resolvable when run as a bare script.

    Byte-identical, intentionally duplicated copy of the algorithm in
    ``anvil.lib.skill_lib_loader.bootstrap_sys_path`` — a bootstrap that
    makes ``anvil`` importable can't itself import from ``anvil`` yet, so
    this can't just delegate to it (issue #1100). See that function's
    docstring for the full layout-resolution explanation, and
    ``tests/lib/test_bootstrap_sys_path_consistency.py`` for the check
    that keeps this copy honest.
    """
    here = Path(__file__).resolve()
    for ancestor in here.parents:
        if (ancestor / "anvil" / "__init__.py").is_file():
            if str(ancestor) not in sys.path:
                sys.path.insert(0, str(ancestor))
            return


def _load_orchestrate() -> ModuleType:
    """Load project-share's ``lib/`` package and return its ``orchestrate``
    submodule.

    Idempotent: re-running is a no-op when the package is already in
    ``sys.modules``. Raises ``ImportError`` when the anvil framework
    itself (``anvil.lib.project_brief``, imported by ``orchestrate``)
    cannot be imported — the caller turns that into a clean exit-1
    with remediation, matching ``render_phase.py``'s framework-import
    guard.
    """
    if _PACKAGE_NAME in sys.modules:
        return getattr(sys.modules[_PACKAGE_NAME], "orchestrate")

    _bootstrap_sys_path()

    lib_dir = Path(__file__).resolve().parent

    pkg_spec = importlib.util.spec_from_file_location(
        _PACKAGE_NAME,
        lib_dir / "__init__.py",
        submodule_search_locations=[str(lib_dir)],
    )
    assert pkg_spec is not None and pkg_spec.loader is not None
    pkg_module = importlib.util.module_from_spec(pkg_spec)
    sys.modules[_PACKAGE_NAME] = pkg_module
    pkg_spec.loader.exec_module(pkg_module)

    orchestrate_module: Optional[ModuleType] = None
    for mod_name in _MODULES:
        full_name = f"{_PACKAGE_NAME}.{mod_name}"
        spec = importlib.util.spec_from_file_location(
            full_name, lib_dir / f"{mod_name}.py"
        )
        assert spec is not None and spec.loader is not None
        module = importlib.util.module_from_spec(spec)
        sys.modules[full_name] = module
        spec.loader.exec_module(module)
        setattr(pkg_module, mod_name, module)
        if mod_name == "orchestrate":
            orchestrate_module = module

    assert orchestrate_module is not None
    return orchestrate_module


FRAMEWORK_IMPORT_REMEDIATION = (
    "project-share cli: could not import the anvil framework "
    "(anvil.lib.project_brief). In a consumer install, run "
    "`uv sync --project .anvil` once, then re-invoke as "
    "`uv run --project .anvil python "
    ".anvil/anvil/skills/project-share/lib/cli.py <project-dir>`."
)


def main(argv: Optional[list] = None) -> int:
    """Parse args, run the export flow, print the report. Returns the
    process exit code (0 on success, 1 otherwise)."""
    parser = argparse.ArgumentParser(
        prog="cli.py",
        description=(
            "Build (or rebuild) a project's share-ready export folder "
            "(orchestrate.run) and print the markdown report. See "
            "commands/project-share.md for the full procedure."
        ),
    )
    parser.add_argument(
        "project_dir",
        help=(
            "Project root: the directory carrying BRIEF.md and the "
            "per-thread <slug>/ directories."
        ),
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the plan and report; write nothing.",
    )
    parser.add_argument(
        "--zip",
        action="store_true",
        dest="zip_output",
        help=(
            "Also write <project>/<dirname>-share-YYYYMMDD.zip "
            "(apply mode only; ignored with --dry-run)."
        ),
    )
    args = parser.parse_args(argv)

    try:
        orchestrate = _load_orchestrate()
    except ImportError:
        print(FRAMEWORK_IMPORT_REMEDIATION, file=sys.stderr)
        return 1

    try:
        result = orchestrate.run(
            Path(args.project_dir),
            dry_run=args.dry_run,
            zip_output=args.zip_output,
        )
    except (FileNotFoundError, ValueError) as exc:
        print(f"project-share cli: {exc}", file=sys.stderr)
        return 1

    print(result.report)
    return 0 if result.success else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())


__all__ = ["FRAMEWORK_IMPORT_REMEDIATION", "main"]
