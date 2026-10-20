"""Pytest sys.path wiring for `anvil:project-scout` tests (issue #407).

Adds the tests directory itself to sys.path so test modules can do
``from _scout_fixtures import ...`` and
``from _project_scout_skill_lib import ...`` without ceremony, and the
repo root so the skill lib's ``anvil.lib.project_detect`` import
resolves when the suite runs standalone
(``pytest anvil/skills/project-scout/tests/`` — the repo-root wiring in
``tests/conftest.py`` does not apply there).

The skill's lib modules are loaded under a unique package name
(``project_scout_lib``) via ``_project_scout_skill_lib`` to avoid the
cross-skill ``lib`` package collision when this suite runs alongside
other per-skill suites that each ship their own ``lib/`` package
(``project-migrate``, ``project-share``, ``rubric-rebackport``). The
helper filename is also unique (per the issue #367 fix — two suites
both shipping ``_skill_lib.py`` collide on
``sys.modules['_skill_lib']``).
"""

from __future__ import annotations

import sys
from pathlib import Path


_HERE = Path(__file__).resolve().parent
# tests/ → project-scout/ → skills/ → anvil/ → repo root.
_REPO_ROOT = _HERE.parents[3]

sys.path.insert(0, str(_HERE))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
