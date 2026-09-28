"""Two-tier rendered output: overview, deep-dive, not-installed, edges (#725)."""

from __future__ import annotations

from _help_fixtures import build_repo, write_manifest
from _help_skill_lib import introspect


def test_overview_lists_only_installed(tmp_path):
    build_repo(tmp_path)
    text = introspect.render_help(tmp_path)
    assert "0.9.0" in text
    assert "memo" in text
    assert "essay" in text
    assert "project-scout" in text
    # A skill NOT installed in the fixture is never listed as an installed
    # bullet (the lifecycle caveat may still NAME ip-uspto/report as examples
    # of documented variations, so we check the bullet line, not raw absence).
    assert "- **ip-uspto**" not in text
    assert "- **datasheet**" not in text


def test_overview_groups_artifact_vs_utility(tmp_path):
    build_repo(tmp_path)
    text = introspect.render_help(tmp_path)
    assert "Artifact skills" in text
    assert "Utility / bridge tools" in text


def test_overview_lifecycle_not_universal(tmp_path):
    build_repo(tmp_path)
    text = introspect.render_help(tmp_path)
    # Acknowledges documented lifecycle variations rather than one diagram.
    assert "essay" in text
    assert "report" in text or "CUSTOMER-READY" in text
    assert "ip-uspto" in text
    assert "no lifecycle" in text.lower() or "one-shot" in text.lower()


def test_overview_start_here_uses_real_command(tmp_path):
    build_repo(tmp_path)
    text = introspect.render_help(tmp_path)
    assert "Start here" in text
    # The pointer names an actually-installed artifact skill's real command.
    assert "-draft" in text


def test_overview_start_here_falls_back_to_utility(tmp_path):
    # Install only a utility skill: pointer must use its direct invocation.
    write_manifest(tmp_path, installed_skills=["project-scout", "help"])
    build_repo(tmp_path)  # writes dirs; overwrite manifest to the subset
    write_manifest(tmp_path, installed_skills=["project-scout", "help"])
    text = introspect.render_help(tmp_path)
    assert "project-scout" in text


def test_deepdive_artifact_skill(tmp_path):
    build_repo(tmp_path)
    text = introspect.render_help(tmp_path, skill="memo")
    assert "memo" in text
    assert "/anvil:memo-draft" in text
    assert "/anvil:memo-review" in text
    assert "44" in text
    assert "≥35" in text
    assert "Thread layout" in text


def test_deepdive_utility_skill_no_rubric(tmp_path):
    build_repo(tmp_path)
    text = introspect.render_help(tmp_path, skill="project-scout")
    assert "project-scout" in text
    assert "No rubric" in text or "one-shot" in text.lower()
    # No lifecycle diagram for a one-shot tool.
    assert "No versioned thread" in text


def test_deepdive_not_installed(tmp_path):
    build_repo(tmp_path)
    text = introspect.render_help(tmp_path, skill="datasheet")
    assert "not installed" in text.lower()
    # Lists what IS installed as a helpful pointer.
    assert "memo" in text


def test_deepdive_manifest_ghost_skill(tmp_path):
    build_repo(tmp_path)
    write_manifest(tmp_path, installed_skills=["memo", "ghost"])
    text = introspect.render_help(tmp_path, skill="ghost")
    assert "not found on disk" in text.lower()


def test_zero_skills_does_not_crash(tmp_path):
    write_manifest(tmp_path, installed_skills=[])
    text = introspect.render_help(tmp_path)
    assert "No Anvil skills" in text


def test_degraded_mode_note_in_overview(tmp_path):
    build_repo(tmp_path, with_manifest=False)
    text = introspect.render_help(tmp_path)
    assert "degraded" in text.lower()
    # Still lists the recovered skills.
    assert "memo" in text


def test_render_against_real_source_repo():
    """Smoke test: render_help over the actual Anvil source checkout."""
    from pathlib import Path

    repo_root = Path(__file__).resolve().parents[4]
    text = introspect.render_help(repo_root)
    # The source repo has anvil/skills/help/ so at least this skill shows.
    assert "help" in text
    assert "Anvil" in text
    # Deep-dive on a real artifact skill resolves its real rubric.
    memo_text = introspect.render_help(repo_root, skill="memo")
    assert "44" in memo_text
