"""Load the project-migrate ``lib/`` package under a unique module name.

This module exists to dodge the cross-skill ``lib`` package name
collision that occurs when multiple per-skill test suites each ship
their own ``lib/`` package (e.g., ``rubric-rebackport``'s tests cache
``lib`` in ``sys.modules``, then ``project-migrate``'s tests can't
import their own ``lib.detect``).

Delegates the actual loading to the shared
``anvil.lib.skill_lib_loader`` helper (issue #879) rather than
re-deriving the ``importlib`` incantation here — that module registers
``lib/`` under the unique package name ``project_migrate_lib`` and
resolves each requested submodule's relative imports (e.g.
``adopt_family.py``'s ``from .adopt_vn import ...``) via normal import
machinery, so no hand-maintained load order is needed. The loaded
modules are exposed as attributes on this module so tests can write
``from _project_migrate_skill_lib import detect, plan, ...``.

Note: This file is named uniquely (``_project_migrate_skill_lib``
rather than the rubric-rebackport precedent's ``_skill_lib``) so
that ``sys.modules['_skill_lib']`` doesn't collide with the
``rubric-rebackport`` helper of the same name when both test suites
run in a single pytest invocation. See issue #367.
"""

from __future__ import annotations

from pathlib import Path

from anvil.lib.skill_lib_loader import load_skill_lib

_HERE = Path(__file__).resolve().parent
_SKILL_ROOT = _HERE.parent
_LIB_DIR = _SKILL_ROOT / "lib"

_PACKAGE_NAME = "project_migrate_lib"

_lib = load_skill_lib(
    "project-migrate",
    _LIB_DIR,
    [
        "detect",
        "plan",
        "apply",
        "enroll",
        "adopt_vn",
        "adopt_family",
        "adopt_review",
        "verify",
        "orchestrate",
    ],
    package_name=_PACKAGE_NAME,
)

# Re-export each submodule on this helper.
detect = _lib.detect
plan = _lib.plan
apply_mod = _lib.apply
enroll = _lib.enroll
adopt_vn = _lib.adopt_vn
adopt_family = _lib.adopt_family
adopt_review = _lib.adopt_review
verify = _lib.verify
orchestrate = _lib.orchestrate


__all__ = [
    "adopt_family",
    "adopt_review",
    "adopt_vn",
    "apply_mod",
    "detect",
    "enroll",
    "orchestrate",
    "plan",
    "verify",
]
