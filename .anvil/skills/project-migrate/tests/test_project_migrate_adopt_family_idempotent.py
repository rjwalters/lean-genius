"""Idempotence + foreign-guard + #346 regressions for `--adopt-family`
(issue #440).

Re-running ``--adopt-family`` (dry-run or ``--apply``) on an adopted
tree finds no letter family and is a successful no-op (zero diff). The
issue's scout-interplay acceptance criterion: post-adopt names must no
longer fire ``find_foreign_families``
(`anvil/skills/project-scout/lib/foreign.py`) on ANY of its three
predicates (dotted stem, letter-series siblings, versioned sidecar
tags). And the #346 additive contract: renamed sidecars holding only a
single-file ``review.md`` payload remain INVISIBLE to
``discover_critics`` until Phase 3 (issue #454) converts their content.
"""

from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

import pytest

from _fixtures import (
    DEFAULT_TAG_MAP,
    build_letter_family_threads,
    write_tag_map,
)
from _project_migrate_skill_lib import orchestrate
from anvil.lib.testing import tree_hash as _tree_digest

run_adopt_family = orchestrate.run_adopt_family

ARTIFACT_TYPE = "ip-uspto-provisional"

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
    name = "project_scout_foreign_for_adopt_family_tests"
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


def _tag_map(tmp_path):
    return write_tag_map(tmp_path / "tag-map.json", DEFAULT_TAG_MAP)


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


class TestAdoptFamilyIdempotent:
    def test_rerun_after_apply_is_noop(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        tag_map = _tag_map(tmp_path)

        first = run_adopt_family(
            project,
            tag_map=tag_map,
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert first.success, first.report
        after_first = _tree_digest(project)

        # Dry-run re-run: no family, success, zero diff.
        second_dry = run_adopt_family(
            project, tag_map=tag_map, artifact_type=ARTIFACT_TYPE
        )
        assert second_dry.success
        assert "nothing to adopt" in second_dry.report
        assert _tree_digest(project) == after_first

        # Apply re-run: still a successful no-op, zero diff.
        second_apply = run_adopt_family(
            project,
            tag_map=tag_map,
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert second_apply.success
        assert second_apply.apply_result is None
        assert _tree_digest(project) == after_first

    def test_rerun_with_existing_brief_is_noop(self, tmp_path):
        project = build_letter_family_threads(
            tmp_path, with_project_brief=True
        )
        tag_map = _tag_map(tmp_path)
        first = run_adopt_family(
            project,
            tag_map=tag_map,
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert first.success, first.report
        after_first = _tree_digest(project)
        second = run_adopt_family(
            project,
            tag_map=tag_map,
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert second.success
        assert _tree_digest(project) == after_first


class TestForeignGuardRegression:
    """AC: ``find_foreign_families`` over the post-adopt names returns
    empty — dotted-stem, letter-series, and versioned-tag predicates
    (i, ii, iii) all go quiet."""

    def test_pre_adopt_names_fire_the_guard(self, tmp_path):
        # Sanity: the fixture genuinely reproduces the foreign shape
        # on all three predicates before adoption.
        foreign = _load_scout_foreign()
        project = build_letter_family_threads(tmp_path)
        families = _families_on_disk(project)
        fired = foreign.find_foreign_families(families)
        assert fired
        whys = "\n".join(w for f in fired for w in f.why)
        assert "contains `.`" in whys  # predicate (i)
        assert "final" in whys and "dot-segment" in whys  # predicate (ii)
        assert "review-v2" in whys  # predicate (iii)

    def test_post_adopt_names_pass_foreign_guard_clean(self, tmp_path):
        foreign = _load_scout_foreign()
        project = build_letter_family_threads(tmp_path)

        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert result.success, result.report

        for slug, versions, sidecars in (
            ("meridian-a", [1, 2], ["meridian-a.2.review"]),
            (
                "meridian-c",
                [5, 7],
                [
                    "meridian-c.5.pre_flight",
                    "meridian-c.5.review",
                    "meridian-c.7.audit",
                    "meridian-c.7.audit2",
                    "meridian-c.7.enablement",
                    "meridian-c.7.s101",
                ],
            ),
        ):
            families = _families_on_disk(project / slug)
            assert [f[0] for f in families] == [slug]
            assert families[0][1] == versions
            assert families[0][2] == sidecars
            assert foreign.find_foreign_families(families) == []


class TestSingleFileReviewStaysInvisible:
    """#346 regression: a renamed sidecar holding only `review.md` is
    NOT a recognizable review payload — `discover_critics` skips it
    (invisible-but-intact until the Phase 3 conversion, issue #454)."""

    def test_discover_critics_skips_review_md_only_sidecars(
        self, tmp_path
    ):
        pytest.importorskip("anvil.lib.critics")
        from anvil.lib.critics import discover_critics

        project = build_letter_family_threads(tmp_path)
        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert result.success, result.report

        for version_dir in (
            project / "meridian-a" / "meridian-a.2",
            project / "meridian-c" / "meridian-c.5",
            project / "meridian-c" / "meridian-c.7",
        ):
            assert discover_critics(version_dir) == []

        # ...and the payloads are intact on disk.
        assert (
            project / "meridian-c" / "meridian-c.5.review" / "review.md"
        ).is_file()
