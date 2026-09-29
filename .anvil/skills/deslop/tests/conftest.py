"""Pytest sys.path wiring for `anvil:deslop` tests (issue #898).

Adds the tests directory itself to sys.path so test modules can do
``from _deslop_skill_lib import ingest, orchestrate`` without ceremony,
and the repo root so the skill lib's ``anvil.lib.*`` imports (rhetoric
lint, project_brief, critics, convergence, review_schema) resolve when
the suite runs standalone (``pytest anvil/skills/deslop/tests/`` — the
repo-root wiring in the top-level ``tests/conftest.py`` does not apply
here).

The skill's lib modules are loaded under a unique package name
(``deslop_lib``) via ``_deslop_skill_lib`` to avoid the cross-skill
``lib`` package name collision when this suite runs alongside other
per-skill suites that each ship their own ``lib/`` package
(``project-photos``, ``project-scout``, ``project-share``,
``project-migrate``, ``rubric-rebackport``). Per the #367 fix, the
helper filename is unique too, so ``sys.modules['_skill_lib']`` never
collides across suites.
"""

from __future__ import annotations

import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
# tests/ -> deslop/ -> skills/ -> anvil/ -> repo root.
_REPO_ROOT = _HERE.parents[3]

sys.path.insert(0, str(_HERE))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
