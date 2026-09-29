"""Idempotence + foreign-guard regression for `--adopt-vn` (issue #432).

Re-running ``--adopt-vn`` (dry-run or ``--apply``) on an adopted tree
finds no ``v{N}`` family and is a successful no-op (zero diff). And the
issue's scout-interplay acceptance criterion: the post-adopt names must
no longer fire ``find_foreign_families``
(`anvil/skills/project-scout/lib/foreign.py`) — the cluster becomes
safe to hand to ``detect_shape``.
"""

from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

from _fixtures import build_vn_report_dirs
from _project_migrate_skill_lib import orchestrate
from anvil.lib.testing import tree_hash as _tree_digest

run_adopt_vn = orchestrate.run_adopt_vn

_SCOUT_FOREIGN_PATH = (
    Path(__file__).resolve().parents[2]
    / "project-scout"
    / "lib"
    / "foreign.py"
)


def _load_scout_foreign():
    """Load project-scout's foreign-guard module by path.

    Stdlib-only module with no intra-lib imports; loaded under a
    unique name to dodge the cross-skill ``lib`` package collision
    (the #358/#367 pattern).
    """
    name = "project_scout_foreign_for_adopt_vn_tests"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(
        name, _SCOUT_FOREIGN_PATH
    )
    module = importlib.util.module_from_spec(spec)
    # Register BEFORE exec: dataclass creation resolves
    # ``cls.__module__`` through sys.modules.
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _families_on_disk(parent: Path):
    """Group ``<stem>.<N>`` version dirs + sidecars under ``parent``.

    Mirrors the name-grouping shape scout's walk feeds the guard:
    ``(stem, version_numbers, sidecar_dir_names)`` tuples.
    """
    version_re = re.compile(r"^(?P<stem>.+)\.(?P<num>\d+)$")
    groups: dict = {}
    names = sorted(d.name for d in parent.iterdir() if d.is_dir())
    for name in names:
        m = version_re.match(name)
        if m is not None:
            groups.setdefault(m.group("stem"), []).append(
                int(m.group("num"))
            )
    out = []
    for stem in sorted(groups):
        sidecar_re = re.compile(
            r"^" + re.escape(stem) + r"\.\d+\..+$"
        )
        sidecars = [n for n in names if sidecar_re.match(n)]
        out.append((stem, sorted(groups[stem]), sidecars))
    return out


class TestAdoptVnIdempotent:
    def test_rerun_after_apply_is_noop(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent

        first = run_adopt_vn(reports, apply=True)
        assert first.success, first.report
        after_first = _tree_digest(project)

        # Dry-run re-run: no family, success, zero diff.
        second_dry = run_adopt_vn(reports)
        assert second_dry.success
        assert "nothing to adopt" in second_dry.report
        assert _tree_digest(project) == after_first

        # Apply re-run: still a successful no-op, zero diff.
        second_apply = run_adopt_vn(reports, apply=True)
        assert second_apply.success
        assert second_apply.apply_result is None
        assert _tree_digest(project) == after_first

    def test_rerun_with_existing_brief_is_noop(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        project = reports.parent
        first = run_adopt_vn(reports, apply=True)
        assert first.success, first.report
        after_first = _tree_digest(project)
        second = run_adopt_vn(reports, apply=True)
        assert second.success
        assert _tree_digest(project) == after_first


class TestForeignGuardRegression:
    """AC: ``find_foreign_families`` over the post-adopt names returns
    empty — the adopted cluster no longer classifies FOREIGN_GRAMMAR."""

    def test_post_adopt_names_pass_foreign_guard_clean(self, tmp_path):
        foreign = _load_scout_foreign()
        reports = build_vn_report_dirs(tmp_path)

        result = run_adopt_vn(reports, apply=True)
        assert result.success, result.report

        families = _families_on_disk(reports)
        # Sanity: the adopted family is visible to the grouping.
        assert [f[0] for f in families] == ["reports"]
        assert families[0][1] == [1, 2, 3, 5]
        assert families[0][2] == ["reports.3.review", "reports.5.review"]

        assert foreign.find_foreign_families(families) == []

    def test_post_adopt_names_pass_with_slug_override(self, tmp_path):
        foreign = _load_scout_foreign()
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent

        result = run_adopt_vn(reports, slug="quarterly", apply=True)
        assert result.success, result.report

        families = _families_on_disk(project / "quarterly")
        assert [f[0] for f in families] == ["quarterly"]
        assert foreign.find_foreign_families(families) == []
