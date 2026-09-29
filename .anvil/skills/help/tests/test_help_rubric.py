"""Rubric-summary extraction against representative Total-line shapes (#725)."""

from __future__ import annotations

import pytest

from _help_fixtures import build_repo, write_skill_dir
from _help_skill_lib import introspect


@pytest.mark.parametrize(
    "line,total,threshold",
    [
        ("| | **Total** | **44** | Advance threshold: ≥35 |", 44, "≥35"),
        ("| | **Total** | **44** | Advance threshold: ≥39 |", 44, "≥39"),
        ("| | **Total** | **45** | | Advance threshold: ≥39 |", 45, "≥39"),
        ("| | **Total** | **49** | Advance threshold: **≥43** | |", 49, "≥43"),
    ],
)
def test_rubric_total_line_variants(line, total, threshold):
    got_total, got_threshold = introspect.parse_rubric_summary(
        "# Rubric\n\n" + line + "\n"
    )
    assert got_total == total
    assert got_threshold == threshold


def test_rubric_unmatched_total_line():
    total, threshold = introspect.parse_rubric_summary(
        "# Rubric\n\n| | **Total** | (varies) | see below |\n"
    )
    assert total is None
    assert threshold is None


def test_rubric_no_total_line_at_all():
    total, threshold = introspect.parse_rubric_summary("# Rubric\n\njust prose\n")
    assert total is None
    assert threshold is None


def test_artifact_skill_rubric_summary_populated(tmp_path):
    build_repo(tmp_path)
    model = introspect.build_model(tmp_path)
    memo = model.find("memo")
    assert memo is not None
    assert memo.rubric_total == 44
    assert memo.rubric_threshold == "≥35"


def test_malformed_rubric_degrades_not_crashes(tmp_path):
    build_repo(tmp_path)
    # Add a skill with a rubric.md whose Total line is unparseable.
    write_skill_dir(
        tmp_path / ".anvil" / "skills",
        "weird",
        description="A skill with an odd rubric.",
        user_invocable=False,
        commands=["weird", "weird-draft"],
        rubric_total=44,
        rubric_malformed=True,
    )
    info = introspect.read_skill_info(tmp_path / ".anvil" / "skills", "weird")
    assert info is not None
    assert info.has_rubric_file is True
    assert info.rubric_total is None  # unmatched → unavailable, not a crash
