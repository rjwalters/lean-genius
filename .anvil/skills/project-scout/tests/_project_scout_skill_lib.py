"""Load the project-scout ``lib/`` package under a unique module name.

This module exists to dodge the cross-skill ``lib`` package name
collision that occurs when multiple per-skill test suites each ship
their own ``lib/`` package (``project-migrate``, ``project-share``,
``rubric-rebackport``). See issues #358 / #367 for the precedent.

Delegates the actual loading to the shared
``anvil.lib.skill_lib_loader`` helper (issue #879) rather than
re-deriving the ``importlib`` incantation here — that module registers
``lib/`` under the unique package name ``project_scout_lib`` and resolves
each requested submodule's relative imports (``from .cluster import
...``) via normal import machinery, so no hand-maintained load order is
needed. The loaded modules are exposed as attributes on this module so
tests can write ``from _project_scout_skill_lib import walk, cluster,
...``.
"""

from __future__ import annotations

from pathlib import Path

from anvil.lib.skill_lib_loader import load_skill_lib

_HERE = Path(__file__).resolve().parent
_SKILL_ROOT = _HERE.parent
_LIB_DIR = _SKILL_ROOT / "lib"

_PACKAGE_NAME = "project_scout_lib"

_lib = load_skill_lib(
    "project-scout",
    _LIB_DIR,
    ["walk", "foreign", "docish", "cluster", "report", "orchestrate"],
    package_name=_PACKAGE_NAME,
)

walk = _lib.walk
foreign = _lib.foreign
docish = _lib.docish
cluster = _lib.cluster
report = _lib.report
orchestrate = _lib.orchestrate


__all__ = [
    "cluster",
    "docish",
    "foreign",
    "orchestrate",
    "report",
    "walk",
]
