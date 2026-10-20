"""Load the deslop ``lib/`` package under a unique module name.

This module exists to dodge the cross-skill ``lib`` package name
collision that occurs when multiple per-skill test suites each ship
their own ``lib/`` package (``project-scout``, ``project-share``,
``project-photos``, ``project-migrate``, ``rubric-rebackport``). See
issues #358 / #367 for the precedent.

Delegates the actual loading to the shared
``anvil.lib.skill_lib_loader`` helper (issue #879) rather than
re-deriving the ``importlib`` incantation here — that module registers
``lib/`` under the unique package name ``deslop_lib`` and resolves each
requested submodule's relative imports via normal import machinery
(``orchestrate.py`` does ``from .ingest import IngestedItem``). The
loaded modules are exposed as attributes on this module so tests can
write ``from _deslop_skill_lib import ingest, orchestrate``.

Note: like project-share, deslop's ``orchestrate`` module imports
``anvil.lib.*`` (rhetoric_lint, project_brief, critics, convergence,
review_schema) — the repo root must be importable, which
``conftest.py`` wires up.
"""

from __future__ import annotations

from pathlib import Path

from anvil.lib.skill_lib_loader import load_skill_lib

_HERE = Path(__file__).resolve().parent
_SKILL_ROOT = _HERE.parent
_LIB_DIR = _SKILL_ROOT / "lib"

_PACKAGE_NAME = "deslop_lib"

_lib = load_skill_lib(
    "deslop",
    _LIB_DIR,
    ["ingest", "orchestrate", "no_fabrication"],
    package_name=_PACKAGE_NAME,
)

ingest = _lib.ingest
orchestrate = _lib.orchestrate
no_fabrication = _lib.no_fabrication


__all__ = [
    "ingest",
    "orchestrate",
    "no_fabrication",
]
