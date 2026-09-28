"""Load the diff ``lib/`` package under a unique module name.

This module exists to dodge the cross-skill ``lib`` package name
collision that occurs when multiple per-skill test suites each ship
their own ``lib/`` package (``project-scout``, ``project-share``,
``project-photos``, ``project-migrate``, ``rubric-rebackport``,
``deslop``). See issues #358 / #367 for the precedent.

Delegates the actual loading to the shared ``anvil.lib.skill_lib_loader``
helper (issue #879) rather than re-deriving the ``importlib`` incantation
here -- that module registers ``lib/`` under the unique package name
``diff_lib`` and resolves each requested submodule's relative imports via
normal import machinery. The loaded modules are exposed as attributes on
this module so tests can write
``from _diff_skill_lib import sources, overlay, server``.
"""

from __future__ import annotations

from pathlib import Path

from anvil.lib.skill_lib_loader import load_skill_lib

_HERE = Path(__file__).resolve().parent
_SKILL_ROOT = _HERE.parent
_LIB_DIR = _SKILL_ROOT / "lib"

_PACKAGE_NAME = "diff_lib"

_lib = load_skill_lib(
    "diff",
    _LIB_DIR,
    ["sources", "overlay", "server"],
    package_name=_PACKAGE_NAME,
)

sources = _lib.sources
overlay = _lib.overlay
server = _lib.server


__all__ = ["sources", "overlay", "server"]
