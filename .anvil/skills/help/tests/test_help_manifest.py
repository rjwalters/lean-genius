"""Manifest parsing + degraded-mode fallback (issue #725)."""

from __future__ import annotations

from _help_fixtures import build_repo, write_codex_shim, write_manifest, write_shim
from _help_skill_lib import introspect


def test_manifest_wellformed(tmp_path):
    build_repo(tmp_path)
    result = introspect.read_manifest(tmp_path)
    assert result.ok is True
    assert result.anvil_version == "0.9.0"
    assert result.installed_skills == ("essay", "help", "memo", "project-scout")
    assert result.skill_versions["memo"] == "0.9.0"
    assert result.reason == ""


def test_manifest_missing_is_soft_fail(tmp_path):
    build_repo(tmp_path, with_manifest=False)
    result = introspect.read_manifest(tmp_path)
    assert result.ok is False
    assert result.installed_skills == ()
    assert "not found" in result.reason


def test_manifest_malformed_json_is_soft_fail(tmp_path):
    build_repo(tmp_path, manifest_raw="{ this is not valid json ")
    result = introspect.read_manifest(tmp_path)
    assert result.ok is False
    assert "JSON" in result.reason


def test_manifest_missing_installed_skills_key(tmp_path):
    build_repo(tmp_path, manifest_raw='{"anvil_version": "0.9.0"}')
    result = introspect.read_manifest(tmp_path)
    assert result.ok is False
    assert "installed_skills" in result.reason


def test_manifest_non_object(tmp_path):
    build_repo(tmp_path, manifest_raw="[1, 2, 3]")
    result = introspect.read_manifest(tmp_path)
    assert result.ok is False


def test_shim_enumeration_fallback(tmp_path):
    build_repo(tmp_path, with_manifest=False)
    names = introspect.enumerate_shim_skills(tmp_path)
    # anvil- prefix stripped, sorted.
    assert names == ("essay", "help", "memo", "project-scout")


def test_shim_enumeration_no_claude_dir(tmp_path):
    assert introspect.enumerate_shim_skills(tmp_path) == ()


def test_shim_enumeration_codex_only(tmp_path):
    """Issue #1004: a Codex-only install (no `.claude/` at all) still
    reports the correct skill list from `.agents/skills/anvil-*/`."""
    write_codex_shim(tmp_path, "memo")
    write_codex_shim(tmp_path, "essay")
    assert introspect.enumerate_shim_skills(tmp_path) == ("essay", "memo")


def test_shim_enumeration_unions_claude_and_codex(tmp_path):
    """Claude-only, Codex-only, and both-registered skills all surface —
    the two shim globs are unioned, not one preferred over the other."""
    write_shim(tmp_path, "memo")
    write_codex_shim(tmp_path, "memo")
    write_shim(tmp_path, "essay")
    write_codex_shim(tmp_path, "project-scout")
    assert introspect.enumerate_shim_skills(tmp_path) == (
        "essay",
        "memo",
        "project-scout",
    )


def test_build_model_degraded_uses_codex_shims_only(tmp_path):
    """`build_model` in degraded mode works from Codex registrations alone
    (issue #1004) — a Codex-only session sees the same install state a
    Claude-only session would."""
    for name in ("memo", "essay"):
        write_codex_shim(tmp_path, name)
    # Reuse build_repo's skill-dir builder indirectly via a minimal manifest-
    # free repo: enumerate_shim_skills only needs the shim dirs, and
    # build_model degrades to unknown_skills when the .anvil/skills/<name>
    # body is absent -- so assert on the enumerated names directly instead
    # of constructing full skill bodies here.
    assert introspect.enumerate_shim_skills(tmp_path) == ("essay", "memo")
    model = introspect.build_model(tmp_path)
    assert model.degraded is True
    assert set(model.unknown_skills) == {"essay", "memo"}


def test_build_model_degraded_uses_shims(tmp_path):
    build_repo(tmp_path, with_manifest=False)
    model = introspect.build_model(tmp_path)
    assert model.degraded is True
    assert model.anvil_version is None
    assert {s.name for s in model.skills} == {
        "essay",
        "help",
        "memo",
        "project-scout",
    }


def test_build_model_manifest_not_degraded(tmp_path):
    build_repo(tmp_path)
    model = introspect.build_model(tmp_path)
    assert model.degraded is False
    assert model.anvil_version == "0.9.0"


def test_skill_named_in_manifest_but_dir_absent(tmp_path):
    build_repo(tmp_path)
    # Manifest names a skill with no on-disk directory.
    write_manifest(
        tmp_path,
        installed_skills=["memo", "ghost"],
        skill_versions={"memo": "0.9.0"},
    )
    model = introspect.build_model(tmp_path)
    assert "ghost" in model.unknown_skills
    assert model.find("ghost") is None
    assert model.find("memo") is not None
