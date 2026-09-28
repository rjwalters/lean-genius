"""Skill enumeration, artifact-vs-utility grouping, command derivation (#725)."""

from __future__ import annotations

from _help_fixtures import build_repo
from _help_skill_lib import introspect


def test_frontmatter_parse():
    fm = introspect.parse_frontmatter(
        "---\nname: memo\ndescription: A memo.\nuser-invocable: false\n---\nbody\n"
    )
    assert fm["name"] == "memo"
    assert fm["description"] == "A memo."
    assert fm["user-invocable"] == "false"


def test_frontmatter_absent():
    assert introspect.parse_frontmatter("no frontmatter here\n") == {}


def test_frontmatter_strips_quotes():
    fm = introspect.parse_frontmatter('---\ndescription: "quoted value"\n---\n')
    assert fm["description"] == "quoted value"


def test_artifact_vs_utility_grouping(tmp_path):
    build_repo(tmp_path)
    model = introspect.build_model(tmp_path)

    artifacts = {s.name for s in model.artifact_skills}
    utils = {s.name for s in model.utility_skills}
    assert artifacts == {"memo", "essay"}
    assert utils == {"project-scout", "help"}


def test_command_set_derivation(tmp_path):
    build_repo(tmp_path)
    model = introspect.build_model(tmp_path)

    memo = model.find("memo")
    assert memo is not None
    assert "memo-draft" in memo.commands
    assert "memo-review" in memo.commands
    # Commands are sorted stems.
    assert list(memo.commands) == sorted(memo.commands)


def test_essay_shorter_lifecycle_reflected_in_commands(tmp_path):
    build_repo(tmp_path)
    model = introspect.build_model(tmp_path)
    essay = model.find("essay")
    assert essay is not None
    assert "essay-status" in essay.commands
    # essay deliberately has no audit / figures command.
    assert "essay-audit" not in essay.commands
    assert "essay-figures" not in essay.commands


def test_utility_skill_has_no_rubric(tmp_path):
    build_repo(tmp_path)
    model = introspect.build_model(tmp_path)
    scout = model.find("project-scout")
    assert scout is not None
    assert scout.is_artifact is False
    assert scout.has_rubric_file is False
    assert scout.user_invocable is True


def test_skill_version_populated_from_manifest(tmp_path):
    build_repo(tmp_path)
    model = introspect.build_model(tmp_path)
    memo = model.find("memo")
    assert memo is not None
    assert memo.version == "0.9.0"
