"""Load the project-share ``lib/`` package under a unique module name.

This module exists to dodge the cross-skill ``lib`` package name
collision that occurs when multiple per-skill test suites each ship
their own ``lib/`` package (e.g., ``rubric-rebackport``'s tests cache
``lib`` in ``sys.modules``, then another skill's tests can't import
their own ``lib.<module>``).

Delegates the actual loading to the shared
``anvil.lib.skill_lib_loader`` helper (issue #879) rather than
re-deriving the ``importlib`` incantation here — that module registers
``lib/`` under the unique package name ``project_share_lib`` and
resolves each requested submodule's relative imports via normal import
machinery, so no hand-maintained load order is needed. The loaded
modules are exposed as attributes on this module so tests can write
``from _project_share_skill_lib import config, plan, ...``.

This file is named uniquely (``_project_share_skill_lib`` rather than
the rubric-rebackport precedent's ``_skill_lib``) so that
``sys.modules['_skill_lib']`` doesn't collide with the helper of the
same name when multiple suites run in a single pytest invocation. See
issue #367 / PR #372 for the precedent.

Note: unlike the bridge-tool libs, project-share's lib modules import
``anvil.lib.*`` (latest_resolution, project_brief) — the repo root must
be importable, which ``conftest.py`` wires up.
"""

from __future__ import annotations

from pathlib import Path

from anvil.lib.skill_lib_loader import load_skill_lib

_HERE = Path(__file__).resolve().parent
_SKILL_ROOT = _HERE.parent
_LIB_DIR = _SKILL_ROOT / "lib"

_PACKAGE_NAME = "project_share_lib"

_lib = load_skill_lib(
    "project-share",
    _LIB_DIR,
    ["config", "collect", "plan", "citations", "apply", "verify", "orchestrate"],
    package_name=_PACKAGE_NAME,
)

# Re-export each submodule on this helper. ``apply`` is exposed as
# ``apply_mod`` to avoid shadowing the builtin in test namespaces
# (mirrors the project-migrate helper).
config = _lib.config
collect = _lib.collect
plan = _lib.plan
citations = _lib.citations
apply_mod = _lib.apply
verify = _lib.verify
orchestrate = _lib.orchestrate


__all__ = [
    "apply_mod",
    "citations",
    "collect",
    "config",
    "orchestrate",
    "plan",
    "verify",
]
