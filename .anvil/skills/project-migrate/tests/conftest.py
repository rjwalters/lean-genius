"""Pytest sys.path wiring for `anvil:project-migrate` tests (issue #297).

Adds the tests directory itself to sys.path so test modules can do
``from _fixtures import ...`` and ``from _project_migrate_skill_lib import ...``
without ceremony.

The skill's lib modules are loaded under a unique package name
(``project_migrate_lib``) via ``_project_migrate_skill_lib`` to
avoid cross-skill collisions when this test suite runs alongside
other per-skill test suites that each ship their own ``lib/``
package (e.g., ``rubric-rebackport``). See issue #358 / PR #362
for the precedent. The helper filename itself is also unique
(rather than the precedent's ``_skill_lib.py``) to dodge the
secondary ``sys.modules['_skill_lib']`` cache collision that arises
when both suites ship identically-named helpers — see issue #367.

The repo root is also added (issue #407): ``lib/detect.py`` is now a
re-export shim over the promoted ``anvil/lib/project_detect.py``, so
the skill lib needs ``anvil.lib.*`` importable even when this suite
runs standalone (``pytest anvil/skills/project-migrate/tests/`` — the
repo-root wiring in ``tests/conftest.py`` does not apply there). Same
shape as project-share's conftest.
"""

from __future__ import annotations

import sys
from pathlib import Path


_HERE = Path(__file__).resolve().parent
# tests/ → project-migrate/ → skills/ → anvil/ → repo root.
_REPO_ROOT = _HERE.parents[3]

sys.path.insert(0, str(_HERE))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
