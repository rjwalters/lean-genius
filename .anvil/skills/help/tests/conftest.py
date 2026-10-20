"""Pytest sys.path wiring for `anvil:help` tests (issue #725).

Adds the tests directory itself to sys.path so test modules can do
``from _help_skill_lib import introspect`` without ceremony.

The skill's lib module is loaded under a unique package name
(``help_skill_lib``) via ``_help_skill_lib`` to avoid the cross-skill
``lib`` package collision when this suite runs alongside other per-skill
suites that each ship their own ``lib/`` package (``project-scout``,
``project-migrate``, ``project-share``, ``rubric-rebackport``). The helper
filename is also unique (per the issue #367 fix — two suites both shipping
``_skill_lib.py`` collide on ``sys.modules['_skill_lib']``).
"""

from __future__ import annotations

import sys
from pathlib import Path


_HERE = Path(__file__).resolve().parent
# tests/ → help/ → skills/ → anvil/ → repo root.
_REPO_ROOT = _HERE.parents[3]

sys.path.insert(0, str(_HERE))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
