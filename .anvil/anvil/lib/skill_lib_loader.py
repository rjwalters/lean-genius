"""Shared loader for a skill's hyphenated ``lib/`` package (issue #879).

Several utility / bridge-tool skills (``project-scout``, ``project-book``,
``project-photos``, ``project-migrate``, ``project-share``,
``rubric-rebackport``, ``help``, ...) ship their Python implementation as a
skill-local ``lib/`` package rather than promoting it into ``anvil/lib/``
(per CLAUDE.md's "skill-local first, lib promotion later" rule). That
creates two invocation footguns every one of these skills' ``commands/*.md``
and vendored ``tests/_<skill>_skill_lib.py`` helpers previously re-derived
by hand:

1. **The hyphen.** Skill directory names like ``project-scout`` are not
   valid Python identifiers, so ``import anvil.skills.project-scout.lib``
   is a syntax error even though ``anvil`` itself is an importable package.
2. **Relative imports.** The lib modules import from siblings
   (``orchestrate.py`` does ``from .cluster import ...``), so the
   directory must be loaded as a *package* — a bare ``sys.path.insert`` +
   ``import orchestrate`` fails with ``ImportError: attempted relative
   import with no known parent package``.

This module is the single place that solves both: it registers a skill's
``lib/`` directory in ``sys.modules`` under a synthetic, collision-safe
package name (default: ``<skill_name with '-' -> '_'>_lib``, e.g.
``project-scout`` -> ``project_scout_lib`` — matching the naming convention
the hand-written vendored helpers already used), then lets *ordinary*
import machinery resolve any submodule's relative imports.

That last point is deliberate and load-bearing: do NOT pre-register stub
submodules in ``sys.modules`` before executing them and then execute them
in some hand-maintained "dependency-safe order" — that breaks intra-package
import graphs where a module needs a *fully executed* sibling to already be
present (``project-migrate``'s ``adopt_family.py`` does
``from .adopt_vn import _FOREIGN_TAG_SUFFIX_RE``; a stub-then-exec sequencer
that gets the order wrong hands it an empty, unexecuted stub with no such
attribute). Instead, this module registers only the package shell up front
and then calls :func:`importlib.import_module` for whichever submodule the
caller actually wants — Python's own import system walks that submodule's
relative imports (and *their* relative imports, transitively) in the
correct order automatically, with no order list to keep in sync as modules
are added or their dependencies change.

Idempotent: repeat calls for the same package name are no-ops (return the
cached ``sys.modules`` entry), so callers can call this on every command
invocation without worrying about double-registration.
"""

from __future__ import annotations

import importlib
import importlib.util
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace
from typing import Iterable

__all__ = [
    "bootstrap_sys_path",
    "default_package_name",
    "import_skill_lib_module",
    "load_skill_lib",
    "load_skill_lib_package",
]


def bootstrap_sys_path(anchor: Path | str) -> None:
    """Make ``import anvil`` resolvable from a bare-script's own file path.

    Walks up from `anchor` (typically a script's own ``Path(__file__)``)
    and inserts the first ancestor directory that contains
    ``anvil/__init__.py`` at the front of ``sys.path`` (a no-op if that
    ancestor is already present). Resolves every supported layout without
    needing to know up front which one applies:

    - source repo: ``<repo>/anvil/skills/<skill>/lib/<file>.py``
      -> inserts ``<repo>``;
    - consumer canonical copy:
      ``<consumer>/.anvil/skills/<skill>/lib/<file>.py``
      -> inserts ``<consumer>/.anvil`` (contains ``anvil/__init__.py``
      post-#230);
    - consumer importable mirror:
      ``<consumer>/.anvil/anvil/skills/<skill>/lib/<file>.py``
      -> inserts ``<consumer>/.anvil``.

    **Not directly callable from the scripts it exists to document**
    (issue #1100). Every bare-script CLI that needs this
    (``anvil/skills/diff/lib/cli.py``, ``anvil/skills/memo/lib/render_phase.py``,
    ``anvil/skills/memo/lib/latest_phase.py``,
    ``anvil/skills/project-share/lib/cli.py``) runs this exact algorithm
    *before* ``anvil`` is importable at all — a bootstrap whose whole job
    is making ``import anvil`` work cannot itself begin with ``from
    anvil.lib.skill_lib_loader import bootstrap_sys_path`` (nothing would
    be on ``sys.path`` yet to resolve that import). Each of those scripts
    therefore keeps its own local, byte-identical copy of this algorithm
    (as ``_bootstrap_sys_path()``) rather than importing it; this function
    is the single canonical, unit-tested reference implementation those
    copies are required to match — drift is caught by
    ``tests/lib/test_bootstrap_sys_path_consistency.py``, not by hand
    cross-referencing docstrings.
    """

    here = Path(anchor).resolve()
    for ancestor in here.parents:
        if (ancestor / "anvil" / "__init__.py").is_file():
            if str(ancestor) not in sys.path:
                sys.path.insert(0, str(ancestor))
            return


def default_package_name(skill_name: str) -> str:
    """Derive the default synthetic package name for `skill_name`.

    Replaces every ``-`` with ``_`` and appends ``_lib``:
    ``project-scout`` -> ``project_scout_lib``,
    ``ip-uspto-provisional`` -> ``ip_uspto_provisional_lib``. Matches the
    naming convention already used by the hand-written vendored test
    loader helpers this module supersedes.
    """

    return f"{skill_name.replace('-', '_')}_lib"


def load_skill_lib_package(
    skill_name: str,
    lib_dir: Path | str,
    *,
    package_name: str | None = None,
) -> ModuleType:
    """Register `lib_dir` as an importable package and return it.

    `lib_dir` must contain an ``__init__.py`` (every Anvil skill lib ships
    one, even when it is empty or docstring-only). The package is
    registered in ``sys.modules`` under `package_name` (default:
    :func:`default_package_name` (`skill_name`)) so it never collides with
    another skill's same-named submodules when multiple per-skill test
    suites each import their own ``lib/`` package in a single pytest run
    (issues #358 / #367).

    Idempotent: a second call with the same effective package name returns
    the already-registered module from ``sys.modules`` without touching
    the filesystem or re-executing ``__init__.py``.

    This loads only the package shell — it does NOT eagerly import every
    submodule. Use :func:`import_skill_lib_module` (or :func:`load_skill_lib`
    for several at once) to load a specific submodule; see the module
    docstring for why submodules are loaded on demand via normal import
    machinery rather than pre-registered as stubs.
    """

    lib_dir = Path(lib_dir).resolve()
    pkg_name = package_name or default_package_name(skill_name)

    existing = sys.modules.get(pkg_name)
    if existing is not None:
        return existing

    init_path = lib_dir / "__init__.py"
    if not init_path.is_file():
        raise FileNotFoundError(
            f"skill lib directory {lib_dir} has no __init__.py; expected "
            "an importable package"
        )

    spec = importlib.util.spec_from_file_location(
        pkg_name, init_path, submodule_search_locations=[str(lib_dir)]
    )
    if spec is None or spec.loader is None:  # pragma: no cover - defensive
        raise ImportError(f"could not build an import spec for {init_path}")

    package = importlib.util.module_from_spec(spec)
    # Register before exec, matching normal import semantics (so a rare
    # self-referential import inside __init__.py itself would resolve).
    sys.modules[pkg_name] = package
    try:
        spec.loader.exec_module(package)
    except BaseException:
        # Don't leave a half-initialized package cached under a name a
        # caller might retry.
        sys.modules.pop(pkg_name, None)
        raise
    return package


def import_skill_lib_module(
    skill_name: str,
    lib_dir: Path | str,
    module_name: str,
    *,
    package_name: str | None = None,
) -> ModuleType:
    """Load one submodule of a skill's ``lib/`` package and return it.

    Ensures the package shell is registered (see
    :func:`load_skill_lib_package`), then imports
    ``<package_name>.<module_name>`` via :func:`importlib.import_module` —
    ordinary import machinery, not a pre-registered stub. `module_name`'s
    own relative imports (``from .cluster import ...``) are resolved
    transitively by that machinery in whatever order they actually need,
    so callers never have to hand-maintain a dependency-safe load order.
    """

    package = load_skill_lib_package(skill_name, lib_dir, package_name=package_name)
    full_name = f"{package.__name__}.{module_name}"
    module = sys.modules.get(full_name)
    if module is None:
        module = importlib.import_module(full_name)
    return module


def load_skill_lib(
    skill_name: str,
    lib_dir: Path | str,
    module_names: Iterable[str],
    *,
    package_name: str | None = None,
) -> SimpleNamespace:
    """Load several submodules of a skill's ``lib/`` package at once.

    Convenience for callers (notably vendored test loader helpers) that
    want a handful of submodules exposed as plain attributes, mirroring
    the shape of the hand-written ``_<skill>_skill_lib.py`` helpers this
    replaces. Returns a :class:`types.SimpleNamespace` with one attribute
    per entry in `module_names` (bound to the loaded submodule) plus
    ``package`` (the package module itself).

    `module_names` does not need to respect intra-package import
    dependencies — see :func:`import_skill_lib_module`.
    """

    package = load_skill_lib_package(skill_name, lib_dir, package_name=package_name)
    ns = SimpleNamespace(package=package)
    for module_name in module_names:
        setattr(
            ns,
            module_name,
            import_skill_lib_module(
                skill_name, lib_dir, module_name, package_name=package.__name__
            ),
        )
    return ns
