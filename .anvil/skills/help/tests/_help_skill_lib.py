"""Load the help ``lib/`` package under a unique module name.

This module exists to dodge the cross-skill ``lib`` package name collision
that occurs when multiple per-skill test suites each ship their own ``lib/``
package (``project-scout``, ``project-migrate``, ``project-share``,
``rubric-rebackport``). See issues #358 / #367 for the precedent.

Delegates the actual loading to the shared ``anvil.lib.skill_lib_loader``
helper (issue #879) rather than re-deriving the ``importlib`` incantation
here — that module registers ``lib/`` under the unique package name
``help_skill_lib``. The loaded module is exposed as an attribute on this
module so tests can write ``from _help_skill_lib import introspect``.
"""

from __future__ import annotations

from pathlib import Path

from anvil.lib.skill_lib_loader import load_skill_lib

_HERE = Path(__file__).resolve().parent
_SKILL_ROOT = _HERE.parent
_LIB_DIR = _SKILL_ROOT / "lib"

_PACKAGE_NAME = "help_skill_lib"

_lib = load_skill_lib(
    "help",
    _LIB_DIR,
    ["introspect"],
    package_name=_PACKAGE_NAME,
)

introspect = _lib.introspect


__all__ = ["introspect"]
