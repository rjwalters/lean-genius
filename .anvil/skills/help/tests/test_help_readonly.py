"""SHA-256 zero-mutation contract for `anvil:help` (issue #725).

The skill is strictly read-only. This test hashes the entire fixture repo
tree before and after every rendering path and asserts byte-for-byte
identity — `render_help` must never write, move, or touch a file.
"""

from __future__ import annotations

from anvil.lib.testing import tree_hash as _tree_hash
from _help_fixtures import build_repo
from _help_skill_lib import introspect


def test_render_help_mutates_nothing(tmp_path):
    build_repo(tmp_path)
    before = _tree_hash(tmp_path)

    introspect.render_help(tmp_path)
    introspect.render_help(tmp_path, skill="memo")
    introspect.render_help(tmp_path, skill="project-scout")
    introspect.render_help(tmp_path, skill="not-installed")

    after = _tree_hash(tmp_path)
    assert before == after


def test_render_help_deterministic(tmp_path):
    build_repo(tmp_path)
    first = introspect.render_help(tmp_path)
    second = introspect.render_help(tmp_path)
    assert first == second
